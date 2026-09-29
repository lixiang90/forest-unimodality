import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell005.Parameters
import ForestUnimodality.BinomialMassData.Q2_7.Batch000_049
import ForestUnimodality.BinomialMassData.Q2_7.Batch050_099
import ForestUnimodality.BinomialMassData.Q2_7.Batch100_149
import ForestUnimodality.BinomialMassData.Q37_126.Batch000_049
import ForestUnimodality.BinomialMassData.Q37_126.Batch050_099
import ForestUnimodality.BinomialMassData.Q37_126.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree000.table
  base := (110607287219866275784596609/20000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (2069350748173766213477975360000000000000)
      constant := (387125505269531965246088131500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree000.table
  base := (110607287219866275784596609/20000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1691)
      previous := (703)
      next := (0)
      square := (24505191701692080538665940560000000000000)
      linear := (37248313467127791842603556480000000000000)
      constant := (6968259094851575374429586367000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree001.table
  base := (799413355271751628256878128430310909549/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (9039857081284790041308951840000000000000)
      constant := (1955201961513148467295686446174261728395050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree001.table
  base := (9887594392638890836954612822105076845553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (1439951655466443906153384257520000000000000)
      constant := (313394928782275882064059119868420399999998856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (28759549773992591449/100000000000000000000)
  directionHi := (575190995479851829/2000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree002.table
  base := (28821361111587872943779424049590723418997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (3594258925353216588272076160000000000000)
      constant := (1407081061849928751364443805949945447530853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree002.table
  base := (2821664484821942532375563874275219356261/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (533259562503836926222744456800000000000000)
      constant := (223138040912272807354453606093486912499998180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28759549773992591449/100000000000000000000)
  centralHi := (575190995479851829/2000000000000000000)
  directionLo := (40672145338124403341/100000000000000000000)
  directionHi := (20336072669062201671/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree003.table
  base := (4136504690908567871913917921280052302667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-1851339230578356864764799520000000000000)
      constant := (1008029028126897125777660878713612814153415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree003.table
  base := (20028679475514366946633093470467784556503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-41492503384307783745321704880000000000000)
      constant := (17568722790704067955398752511812585978835646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40672145338124403341/100000000000000000000)
  centralHi := (20336072669062201671/50000000000000000000)
  directionLo := (4981300141136119047/10000000000000000000)
  directionHi := (49813001411361190471/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree004.table
  base := (14711405570319218872565148504578642267753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-7296937386509930317801675200000000000000)
      constant := (716751148459523762940524189684353471119897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree004.table
  base := (3520371495514346328500577747054974725663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-1280124623421377033638535144640000000000000)
      constant := (111152467350567017756828390818089557489251576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4981300141136119047/10000000000000000000)
  centralHi := (49813001411361190471/100000000000000000000)
  directionLo := (28759549773992591449/50000000000000000000)
  directionHi := (57519099547985182899/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree005.table
  base := (1030244860004740932224975031242301889159/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-12742535542441503770838550880000000000000)
      constant := (503575038763198156987732567708727925687910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree005.table
  base := (1946371916256551290328817783612622536009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-2186816716383984013569174945360000000000000)
      constant := (77134168019205308921820432252684988454197210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28759549773992591449/50000000000000000000)
  centralHi := (57519099547985182899/100000000000000000000)
  directionLo := (2572332331877445913/4000000000000000000)
  directionHi := (32154154148468073913/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree006.table
  base := (1410304662334769006502302395190317336899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-18188133698373077223875426560000000000000)
      constant := (348698366667295589789803743141627747540255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree006.table
  base := (1310725192983793908040378283073912866013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-343723201038510110388868305120000000000000)
      constant := (5853403940354692467723635041715955739117330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2572332331877445913/4000000000000000000)
  centralHi := (32154154148468073913/50000000000000000000)
  directionLo := (14089244435691424127/20000000000000000000)
  directionHi := (17611555544614280159/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree007.table
  base := (4623795510822591631889910312304119274441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-3376247407757807239558900320000000000000)
      constant := (33673465235342182449310297146128834921087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree007.table
  base := (4199647718887838107177387554388281470687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-571457271758456853347207792400000000000000)
      constant := (5005184698510734771601927042536311187759058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14089244435691424127/20000000000000000000)
  centralHi := (17611555544614280159/25000000000000000000)
  directionLo := (76090616520168248833/100000000000000000000)
  directionHi := (38045308260084124417/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree008.table
  base := (2790016031712155808402881576455968616267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-29079330010236224129949177920000000000000)
      constant := (153389499580204046766716454846342462197083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree008.table
  base := (2434334290283028256106956456874172944771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-4906892995271804953361094347520000000000000)
      constant := (22331022489383564026794531488107184835592198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76090616520168248833/100000000000000000000)
  centralHi := (38045308260084124417/50000000000000000000)
  directionLo := (40672145338124403341/50000000000000000000)
  directionHi := (81344290676248806683/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree009.table
  base := (1388245805885748367433771698121560532607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-34524928166167797582986053600000000000000)
      constant := (93789081111339228118220818167956466097743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree009.table
  base := (546477570931086614217108682942102502059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-645953898692712437032414905360000000000000)
      constant := (1473021473109731861870587944209868813632076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40672145338124403341/50000000000000000000)
  centralHi := (81344290676248806683/100000000000000000000)
  directionLo := (86278649321977774347/100000000000000000000)
  directionHi := (21569662330494443587/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree010.table
  base := (30170878280581908194786211324708529589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-39970526322099371036022929280000000000000)
      constant := (51190974764460860074983960349107179498610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree010.table
  base := (57974813252087605248937833788908340439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-6720277181197018913222373948960000000000000)
      constant := (6881808710944865736026344157816354406404782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86278649321977774347/100000000000000000000)
  centralHi := (21569662330494443587/25000000000000000000)
  directionLo := (22736420441699333681/25000000000000000000)
  directionHi := (3637827270671893389/4000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree011.table
  base := (-553880498149770972462978316068227454427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-45416124478030944489059804960000000000000)
      constant := (21465192969084135341007455632656854733077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree011.table
  base := (-754557935364071183656428610632267762097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-7626969274159625893153013749680000000000000)
      constant := (2538463906589304642060185579341058504474014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22736420441699333681/25000000000000000000)
  centralHi := (3637827270671893389/4000000000000000000)
  directionLo := (95384635739883865727/100000000000000000000)
  directionHi := (745192466717842701/781250000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree012.table
  base := (-1239433545093806847189700947367079933747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-50861722633962517942096680640000000000000)
      constant := (1627071827682586398134687499013083246397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree012.table
  base := (-175586677220451540288223518207396866169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-948184596346914763675961505600000000000000)
      constant := (-27724505093708536427216831191392287688464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95384635739883865727/100000000000000000000)
  centralHi := (745192466717842701/781250000000000000)
  directionLo := (4981300141136119047/5000000000000000000)
  directionHi := (99626002822722380941/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree013.table
  base := (-22488009997859316858257904226004274647/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-56307320789894091395133556320000000000000)
      constant := (-10483820308064170268622345365936756616240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree013.table
  base := (-967732486439996247294964000959269541149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-9440353460084839853014293351120000000000000)
      constant := (-1823743290806957830414136059089363235281524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4981300141136119047/5000000000000000000)
  centralHi := (99626002822722380941/100000000000000000000)
  directionLo := (10369403136938907311/10000000000000000000)
  directionHi := (103694031369389073111/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree014.table
  base := (-1132340253221559643611990083020934110591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-8821845563689380692595776000000000000000)
      constant := (-2347773914070606052332259882293077548274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree014.table
  base := (-118889096540528124315491012805480198461/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-1478149364721063833277847593120000000000000)
      constant := (-347080370087744129047926357228290901095480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10369403136938907311/10000000000000000000)
  centralHi := (103694031369389073111/100000000000000000000)
  directionLo := (53804190926076108153/50000000000000000000)
  directionHi := (107608381852152216307/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree015.table
  base := (-664900640467018578371123713730956210781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-67198517101757238301207307680000000000000)
      constant := (-17363964393233766774608504691267417313076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree015.table
  base := (-27539077435124524491151165573716016189/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-1250415294001117090319508105840000000000000)
      constant := (-249300636322314354489325732901752627869800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53804190926076108153/50000000000000000000)
  centralHi := (107608381852152216307/100000000000000000000)
  directionLo := (111385257319096586843/100000000000000000000)
  directionHi := (27846314329774146711/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree016.table
  base := (-375095084858196964903394942718804455399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-72644115257688811754244183360000000000000)
      constant := (-14103193217619042790934575625771346516408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree016.table
  base := (-3079933053963843062104810973040724421339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-12160429738972660792806212753280000000000000)
      constant := (-1393900223627616922307292252157270456588982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111385257319096586843/100000000000000000000)
  centralHi := (27846314329774146711/25000000000000000000)
  directionLo := (28759549773992591449/25000000000000000000)
  directionHi := (115038199095970365797/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree017.table
  base := (-1650280554615440836667096487242503985843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-78089713413620385207281059040000000000000)
      constant := (-7260010209617720690532750629765390612614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree017.table
  base := (-134701394686359499804367554092930786333/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-13067121831935267772736852554000000000000000)
      constant := (27161853561046238841628429277885452216150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28759549773992591449/25000000000000000000)
  centralHi := (115038199095970365797/100000000000000000000)
  directionLo := (59289330731689985919/50000000000000000000)
  directionHi := (118578661463379971839/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree018.table
  base := (-3568120566066554578688224439620807840307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-83535311569551958660317934720000000000000)
      constant := (2718865688744641785348135258580415824957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree018.table
  base := (-362522861360301220418044557302450655269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-1552645991655319416963054706080000000000000)
      constant := (216876113035051831655611504352385220527420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59289330731689985919/50000000000000000000)
  centralHi := (118578661463379971839/100000000000000000000)
  directionLo := (15252054501796651253/12500000000000000000)
  directionHi := (4880657440574928401/4000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree019.table
  base := (-476271456186020628435563213912709808907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-88980909725483532113354810400000000000000)
      constant := (15503537071805085619140745106217754908456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree019.table
  base := (-385925994134767006606224652347796918337/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-14880506017860481732598132155440000000000000)
      constant := (4330691313400829480278117224931880622408940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15252054501796651253/12500000000000000000)
  centralHi := (4880657440574928401/4000000000000000000)
  directionLo := (62679985563280861847/50000000000000000000)
  directionHi := (25071994225312344739/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree020.table
  base := (-4031715059105800909214880609381349996453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-94426507881415105566391686080000000000000)
      constant := (30848969658669304225744731740313850173803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree020.table
  base := (-4074240492464086319628046926238523331067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-15787198110823088712528771956160000000000000)
      constant := (7126973527056543078796981929918601797990154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62679985563280861847/50000000000000000000)
  centralHi := (25071994225312344739/20000000000000000000)
  directionLo := (2572332331877445913/2000000000000000000)
  directionHi := (128616616593872295651/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree021.table
  base := (-1059122465757157445669090040235040299123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-14267443719620954145632651680000000000000)
      constant := (6938849873141155317729507833418871624556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree021.table
  base := (-2136800843985280505059132419002868171567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1691)
      previous := (703)
      next := (0)
      square := (24505191701692080538665940560000000000000)
      linear := (-264982384187074534800943043760000000000000)
      constant := (163706238702211770179978716191277220765116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2572332331877445913/2000000000000000000)
  centralHi := (128616616593872295651/100000000000000000000)
  directionLo := (32948203448042792789/25000000000000000000)
  directionHi := (131792813792171171157/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree022.table
  base := (-2213656492904939166910646478356118869363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-105317704193278252472465437440000000000000)
      constant := (68534446128653327002561133441100350802426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree022.table
  base := (-2229959541961793865659322049865152142097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-17600582296748302672390051557600000000000000)
      constant := (13869805082972778660431914185860844592068028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32948203448042792789/25000000000000000000)
  centralHi := (131792813792171171157/100000000000000000000)
  directionLo := (67447122752680601271/50000000000000000000)
  directionHi := (134894245505361202543/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree023.table
  base := (-1151581161700002836217249157394602061403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-110763302349209825925502313120000000000000)
      constant := (90631589960492249232361903550657995965012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree023.table
  base := (-2317572313649892804546638317550872702157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-18507274389710909652320691358320000000000000)
      constant := (17780415106156451874967585437102344980555468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67447122752680601271/50000000000000000000)
  centralHi := (134894245505361202543/100000000000000000000)
  directionLo := (68962977701197434431/50000000000000000000)
  directionHi := (137925955402394868863/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree024.table
  base := (-4775166123796602189910384755622836753501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-116208900505141399378539188800000000000000)
      constant := (114782957995423758583054099934480999078451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree024.table
  base := (-4800773326715833522523115882035962179373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-2157107386963724070250147906560000000000000)
      constant := (2448161747710129358089007164844281357793014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68962977701197434431/50000000000000000000)
  centralHi := (137925955402394868863/100000000000000000000)
  directionLo := (140892444356914241271/100000000000000000000)
  directionHi := (17611555544614280159/12500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree025.table
  base := (-4935108784328430688479821363745664425131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-121654498661072972831576064480000000000000)
      constant := (140926253224537643897453885176462443168581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree025.table
  base := (-4957963177030808041868604761069458709961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-20320658575636123612181970959760000000000000)
      constant := (26619734789485565889204955422130636760329582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140892444356914241271/100000000000000000000)
  centralHi := (17611555544614280159/12500000000000000000)
  directionLo := (71898874434981478623/50000000000000000000)
  directionHi := (143797748869962957247/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree026.table
  base := (-1271786998157572025815266337472375268659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-127100096817004546284612940160000000000000)
      constant := (169012702800329133304057073375414447342836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree026.table
  base := (-127690543192667905644745586388813462501/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-21227350668598730592112610760480000000000000)
      constant := (31532048158810244842535541757263949386682480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71898874434981478623/50000000000000000000)
  centralHi := (143797748869962957247/100000000000000000000)
  directionLo := (146645505499731188541/100000000000000000000)
  directionHi := (73322752749865594271/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree027.table
  base := (-5232071671712205066008201595312530104027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-132545694972936119737649815840000000000000)
      constant := (199003698495306725846913505349686024902677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree027.table
  base := (-164077150501172448511916113957190062053/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-2459338084617926396893694506800000000000000)
      constant := (4084964640991749377253148416452267688616128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146645505499731188541/100000000000000000000)
  centralHi := (73322752749865594271/50000000000000000000)
  directionLo := (14943900423408357141/10000000000000000000)
  directionHi := (149439004234083571411/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree028.table
  base := (-5370510551623467996127563029128644421917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-19713041875552527598669527360000000000000)
      constant := (32981190648150769567873266796099489046581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree028.table
  base := (-2693541119608042246219576745798202324019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-3291533550646277793139127194560000000000000)
      constant := (6044721295102151703636302372849677129124908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14943900423408357141/10000000000000000000)
  centralHi := (149439004234083571411/100000000000000000000)
  directionLo := (76090616520168248833/50000000000000000000)
  directionHi := (152181233040336497667/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree029.table
  base := (-5502975161905327608633989200412865718889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-143436891284799266643723567200000000000000)
      constant := (264581594978053831652928022139769579774439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree029.table
  base := (-5517931188114149148426145527092911052291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-23947426947486551531904530162640000000000000)
      constant := (48173425612038368952513110179036472066914042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76090616520168248833/50000000000000000000)
  centralHi := (152181233040336497667/100000000000000000000)
  directionLo := (38718728827984495683/25000000000000000000)
  directionHi := (154874915311937982733/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree030.table
  base := (-703735401171491953331395397650474842919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-148882489440730840096760442880000000000000)
      constant := (300123012184408625447298498521013861575752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree030.table
  base := (-5643400879560627120181161040370848088887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-2761568782272128723537241107040000000000000)
      constant := (6038083728523082199481596894792911985601666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38718728827984495683/25000000000000000000)
  centralHi := (154874915311937982733/100000000000000000000)
  directionLo := (157522541549083442717/100000000000000000000)
  directionHi := (78761270774541721359/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree031.table
  base := (-2875789982335561418465422699299198047103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-154328087596662413549797318560000000000000)
      constant := (337475667894376059807388035788678591383906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree031.table
  base := (-2881905419433088769812638701623255750619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-25760811133411765491765809764080000000000000)
      constant := (60818496507807162264728390054769191703172756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157522541549083442717/100000000000000000000)
  centralHi := (78761270774541721359/50000000000000000000)
  directionLo := (32025279264534432381/20000000000000000000)
  directionHi := (80063198161336080953/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree032.table
  base := (-2934176774926700918774628367106520134079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-159773685752593987002834194240000000000000)
      constant := (376625444127481017427461810743561026860258) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree032.table
  base := (-2939714292006143253443072627804483888047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-26667503226374372471696449564800000000000000)
      constant := (67598530907599599697881873404496013793365828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32025279264534432381/20000000000000000000)
  centralHi := (80063198161336080953/50000000000000000000)
  directionLo := (32537716270499522673/20000000000000000000)
  directionHi := (81344290676248806683/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree033.table
  base := (-1196089298712156277314309702412801763393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-165219283908525560455871069920000000000000)
      constant := (417560456980265069162327408508863567968715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree033.table
  base := (-1497619991184828538938879201114427569023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-3063799479926331050180787707280000000000000)
      constant := (8297895995649563705861765898128299536486856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32537716270499522673/20000000000000000000)
  centralHi := (81344290676248806683/50000000000000000000)
  directionLo := (82605517681464522571/50000000000000000000)
  directionHi := (165211035362929045143/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree034.table
  base := (-3044032271211829978357955884741444151429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-170664882064457133908907945600000000000000)
      constant := (460270624867838689848793468255338473159958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree034.table
  base := (-1219431411027761993742815628652777557157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-28480887412299586431557729166240000000000000)
      constant := (82064570983407863437418762880771258756438670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82605517681464522571/50000000000000000000)
  centralHi := (165211035362929045143/100000000000000000000)
  directionLo := (83847775624779917009/50000000000000000000)
  directionHi := (167695551249559834019/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree035.table
  base := (-1238276689040111540245203946681980013019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-25158640031484101051706403040000000000000)
      constant := (72106762300147770282560000266130699544335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree035.table
  base := (-3099812122849341788814147238129977142819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-4198225643608884773069766995280000000000000)
      constant := (12821106720513134756302068858021211840086508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83847775624779917009/50000000000000000000)
  centralHi := (167695551249559834019/100000000000000000000)
  directionLo := (85071895494482350999/50000000000000000000)
  directionHi := (170143790988964701999/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree036.table
  base := (-6290554230245597011349841916314851916201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-181556078376320280814981696960000000000000)
      constant := (550983190290500178378556503220572256106151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree036.table
  base := (-314901150027602340276192998251843973667/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-3366030177580533376824334307520000000000000)
      constant := (10858829911012185696851676689397472304514120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85071895494482350999/50000000000000000000)
  centralHi := (170143790988964701999/100000000000000000000)
  directionLo := (34511459728791109739/20000000000000000000)
  directionHi := (21569662330494443587/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree037.table
  base := (-798213419451371476583652507058105590199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-187001676532251854268018572640000000000000)
      constant := (598971794991678546697192727153222608641992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree037.table
  base := (-3196237808495909988256969828736558021671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-31200963691187407371349648568400000000000000)
      constant := (106008766654049845837260283325998404847951204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34511459728791109739/20000000000000000000)
  centralHi := (21569662330494443587/12500000000000000000)
  directionLo := (87468755876744383877/50000000000000000000)
  directionHi := (34987502350697753551/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree038.table
  base := (-1295391201821124015429796176912928948801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-192447274688183427721055448320000000000000)
      constant := (648707604001931536307552163856332407543755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree038.table
  base := (-1296617646452037268294130606517412663937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-32107655784150014351280288369120000000000000)
      constant := (114584796890984016345477176945963891368340470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87468755876744383877/50000000000000000000)
  centralHi := (34987502350697753551/20000000000000000000)
  directionLo := (11080360709117699539/6250000000000000000)
  directionHi := (1418286170767065541/800000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree039.table
  base := (-820549845237170816320665693339773431613/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-197892872844115001174092324000000000000000)
      constant := (700185787334035735646600957170808814807704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree039.table
  base := (-6569953256643331099189920839460702898923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-3668260875234735703467880907760000000000000)
      constant := (13717425150784493854252639128695660043149914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11080360709117699539/6250000000000000000)
  centralHi := (1418286170767065541/800000000000000000)
  directionLo := (89801665386711419549/50000000000000000000)
  directionHi := (179603330773422839099/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree040.table
  base := (-664812172583869897399689215335991092149/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-203338471000046574627129199680000000000000)
      constant := (753402125507219242461485839685364364846990) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree040.table
  base := (-6653151364496264227844069189000430038447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-33921039970075228311141567970560000000000000)
      constant := (132624214659249061658918084294514586354807714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89801665386711419549/50000000000000000000)
  centralHi := (179603330773422839099/100000000000000000000)
  directionLo := (181891363533594669449/100000000000000000000)
  directionHi := (3637827270671893389/2000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree041.table
  base := (-3364100162962636721914448701928524102759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-208784069155978148080166075360000000000000)
      constant := (808352922696694910969331193131004637929618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree041.table
  base := (-1683188285165063208187825849967419366323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-34827732063037835291072207771280000000000000)
      constant := (142086401495079888975394259535174500280512104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181891363533594669449/100000000000000000000)
  centralHi := (3637827270671893389/2000000000000000000)
  directionLo := (18415097021550836791/10000000000000000000)
  directionHi := (184150970215508367911/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree042.table
  base := (-6804700771073643936585882465219086930411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-30604238187415674504743278720000000000000)
      constant := (123576419237935942191490642903466391487123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree042.table
  base := (-6808820455028276760136189869856537832867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1691)
      previous := (703)
      next := (0)
      square := (24505191701692080538665940560000000000000)
      linear := (-567213081841276861444489644000000000000000)
      constant := (2410204694307023057434470949438076233058758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18415097021550836791/10000000000000000000)
  centralHi := (184150970215508367911/100000000000000000000)
  directionLo := (11648949043012522873/6250000000000000000)
  directionHi := (186383184688200365969/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree043.table
  base := (-6877681285793486062614332120612821906679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-219675265467841294986239826720000000000000)
      constant := (923445308412815190667818006889971726572729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree043.table
  base := (-6881407620068020428103630648173964479757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-36641116248963049250933487372720000000000000)
      constant := (161893266265668273676933602666135069959688934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11648949043012522873/6250000000000000000)
  centralHi := (186383184688200365969/100000000000000000000)
  directionLo := (47147244907389978813/25000000000000000000)
  directionHi := (188588979629559915253/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree044.table
  base := (-6947193150218311452589746144892080642073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-225120863623772868439276702400000000000000)
      constant := (983581531211943627048382223860288048538423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree044.table
  base := (-1737640593252553747961082803646662148603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-37547808341925656230864127173440000000000000)
      constant := (172237134129919808241176237991411183457557544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47147244907389978813/25000000000000000000)
  centralHi := (188588979629559915253/100000000000000000000)
  directionLo := (95384635739883865727/50000000000000000000)
  directionHi := (38153854295953546291/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree045.table
  base := (-7013281584828608980678124567375215420547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-230566461779704441892313578080000000000000)
      constant := (1045441387259392949647993149798614444393197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree045.table
  base := (-438520419674213505982666616857226468409/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-4272722270543140356754974108240000000000000)
      constant := (20319351770077158845126130288010820077812192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95384635739883865727/50000000000000000000)
  centralHi := (38153854295953546291/20000000000000000000)
  directionLo := (7716996995632337739/4000000000000000000)
  directionHi := (48231231222702110869/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree046.table
  base := (-7075986507959279829396672482202768321033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-236012059935636015345350453760000000000000)
      constant := (1109022920556753000523307735092064352269383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree046.table
  base := (-7078737630691299767457868358140471695209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-39361192527850870190725406774880000000000000)
      constant := (193804068078746813463775129003720935683430958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7716996995632337739/4000000000000000000)
  centralHi := (48231231222702110869/25000000000000000000)
  directionLo := (97528378366666740943/50000000000000000000)
  directionHi := (195056756733333481887/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree047.table
  base := (-89191789850519140750873123240453300927/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-241457658091567588798387329440000000000000)
      constant := (1174324402950894623869427441217423060366160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree047.table
  base := (-7137827712410619800498226512261937740339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-40267884620813477170656046575600000000000000)
      constant := (205026581861251632201703598412684738217189018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97528378366666740943/50000000000000000000)
  centralHi := (195056756733333481887/100000000000000000000)
  directionLo := (197165539713535118407/100000000000000000000)
  directionHi := (24645692464191889801/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree048.table
  base := (-7191382807919978687075477718220589277969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-246903256247499162251424205120000000000000)
      constant := (1241344306482431664381839038207191125379519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree048.table
  base := (-7193625697120513194189100454885538720553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-4574952968197342683398520708480000000000000)
      constant := (24060164351390294257679679129350954848472254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197165539713535118407/100000000000000000000)
  centralHi := (24645692464191889801/12500000000000000000)
  directionLo := (4981300141136119047/2500000000000000000)
  directionHi := (199252005645444761881/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree049.table
  base := (-7244132955098291354635603257914000743913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-36049836343347247957780154400000000000000)
      constant := (187154468480526332727666030474601994792609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree049.table
  base := (-7246156936261215396594447688639833799839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-6011609829534098732931046596720000000000000)
      constant := (32621222677542467547040567943182428470982574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4981300141136119047/2500000000000000000)
  centralHi := (199252005645444761881/100000000000000000000)
  directionLo := (12582303026121758759/6250000000000000000)
  directionHi := (40263369683589628029/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree050.table
  base := (-3646809024552245736068832627599843152639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-257794452559362309157497956480000000000000)
      constant := (1380534125037779529744912466495215371041378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree050.table
  base := (-1459088760863030048047083932113752362917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-42987960899701298110447965977760000000000000)
      constant := (240447642993464025349651288540405168715824270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12582303026121758759/6250000000000000000)
  centralHi := (40263369683589628029/20000000000000000000)
  directionLo := (203360726690622016707/100000000000000000000)
  directionHi := (50840181672655504177/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree051.table
  base := (-1467971943022965086980900707900537810497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-263240050715293882610534832160000000000000)
      constant := (1452701783871081192964770646084368236428235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree051.table
  base := (-7341506056082005026829557561537269889687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-4877183665851545010042067308720000000000000)
      constant := (28093175011212554231020578778384127957296066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203360726690622016707/100000000000000000000)
  centralHi := (50840181672655504177/25000000000000000000)
  directionLo := (102692133174041894587/50000000000000000000)
  directionHi := (8215370653923351567/4000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree052.table
  base := (-3691438555688312741958369905555473821639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-268685648871225456063571707840000000000000)
      constant := (1526583317109470038945186288775563565479378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree052.table
  base := (-295374445581161478732592228292100960209/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-44801345085626512070309245579200000000000000)
      constant := (265521216563180073269522335018952564446523950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102692133174041894587/50000000000000000000)
  centralHi := (8215370653923351567/4000000000000000000)
  directionLo := (10369403136938907311/5000000000000000000)
  directionHi := (207388062738778146221/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree053.table
  base := (-7422687216711828702281942307743671351267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-274131247027157029516608583520000000000000)
      constant := (1602177892790671150613888550920560103787917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree053.table
  base := (-7424024470162200651674057709238475496303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-45708037178589119050239885379920000000000000)
      constant := (278495445011979013409192457093804981510346786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10369403136938907311/5000000000000000000)
  centralHi := (207388062738778146221/100000000000000000000)
  directionLo := (104686341360449379601/50000000000000000000)
  directionHi := (209372682720898759203/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree054.table
  base := (-3729652541690242150386511312166937671639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-279576845183088602969645459200000000000000)
      constant := (1679484773353942116643004764367640108179378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree054.table
  base := (-932563708994070593623224307339103493243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-5179414363505747336685613908960000000000000)
      constant := (32417905811136385042137399323815285751677392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104686341360449379601/50000000000000000000)
  centralHi := (209372682720898759203/100000000000000000000)
  directionLo := (211338666535371361907/100000000000000000000)
  directionHi := (52834666633842840477/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree055.table
  base := (-3746372029888228515025505268256597971867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-285022443339020176422682334880000000000000)
      constant := (1758503304727983564250144470110853398757034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree055.table
  base := (-7493828789110461985165595569440562817597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-47521421364514333010101164981360000000000000)
      constant := (305318242820983808009274874506880812353915014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211338666535371361907/100000000000000000000)
  centralHi := (52834666633842840477/25000000000000000000)
  directionLo := (213286529523436271989/100000000000000000000)
  directionHi := (21328652952343627199/10000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree056.table
  base := (-1504603197354090565355455069472013305179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-41495434499278821410817030080000000000000)
      constant := (262747558101447271791271510328479534318735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree056.table
  base := (-3761996236194465575659575633782713418137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-6918301922496705712861686397440000000000000)
      constant := (45595233146938631339358618550900805967665284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213286529523436271989/100000000000000000000)
  centralHi := (21328652952343627199/10000000000000000000)
  directionLo := (53804190926076108153/25000000000000000000)
  directionHi := (215216763704304432613/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree057.table
  base := (-3775065685487460368886274375273696002329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-295913639650883323328756086240000000000000)
      constant := (1921673064476374128215057217943177791771758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree057.table
  base := (-7551010143090036141331385111315589958637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-5481645061159949663329160509200000000000000)
      constant := (37034027237410168476476048528599649656482166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53804190926076108153/25000000000000000000)
  centralHi := (215216763704304432613/100000000000000000000)
  directionLo := (27141229903321546719/12500000000000000000)
  directionHi := (217129839226572373753/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree058.table
  base := (-3787049768878132927606574518476628922937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-301359237806814896781792961920000000000000)
      constant := (2005823321083759391761974810789290365552174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree058.table
  base := (-3787445068760704729641039037345602373223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-50241497643402153949893084383520000000000000)
      constant := (347737015971737111930211893838541216722711652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27141229903321546719/12500000000000000000)
  centralHi := (217129839226572373753/100000000000000000000)
  directionLo := (219026205705527219769/100000000000000000000)
  directionHi := (21902620570552721977/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree059.table
  base := (-1898732191610818909787961943887687027871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-306804835962746470234829837600000000000000)
      constant := (2091683270845176107637067543958013342537284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree059.table
  base := (-759563983428982695806608325948616698343/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-51148189736364760929823724184240000000000000)
      constant := (362458885962326619581013357177698806485532660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219026205705527219769/100000000000000000000)
  centralHi := (21902620570552721977/10000000000000000000)
  directionLo := (55226573364279696271/25000000000000000000)
  directionHi := (44181258691423757017/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree060.table
  base := (-761262640986239168032103838715881085901/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-312250434118678043687866713280000000000000)
      constant := (2179252553472128637894448139829218267908510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree060.table
  base := (-3806632883255749123738272999769494215143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-5783875758814151989972707109440000000000000)
      constant := (41941311472064840817572315457206612204487748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55226573364279696271/25000000000000000000)
  centralHi := (44181258691423757017/20000000000000000000)
  directionLo := (111385257319096586843/50000000000000000000)
  directionHi := (222770514638193173687/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree061.table
  base := (-7627199000059471974466128275177152161727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-317696032274609617140903588960000000000000)
      constant := (2268530848894369940742591635636319544075377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree061.table
  base := (-953471715094443389791636707772767946057/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-52961573922289974889685003785680000000000000)
      constant := (392775721896722250610098137608138144353596272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111385257319096586843/50000000000000000000)
  centralHi := (222770514638193173687/100000000000000000000)
  directionLo := (112309632150773466497/50000000000000000000)
  directionHi := (44923852860309386599/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree062.table
  base := (-3819326170917742976892943155260730493501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-323141630430541190593940464640000000000000)
      constant := (2359517872676652514003758356704448411636902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree062.table
  base := (-305566752972416457522949032741637366709/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-53868266015252581869615643586400000000000000)
      constant := (408370601206327049545132412061942064576598950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112309632150773466497/50000000000000000000)
  centralHi := (44923852860309386599/20000000000000000000)
  directionLo := (226452921373452265097/100000000000000000000)
  directionHi := (113226460686726132549/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree063.table
  base := (-955873949440439461943469421225878053629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-46941032655210394863853905760000000000000)
      constant := (350316195994665047984549086011350828996776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree063.table
  base := (-477965976385419236863758558297388132129/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1691)
      previous := (703)
      next := (0)
      square := (24505191701692080538665940560000000000000)
      linear := (-869443779495479188088036244240000000000000)
      constant := (6734228652369245233752915108252465525627936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226452921373452265097/100000000000000000000)
  centralHi := (113226460686726132549/50000000000000000000)
  directionLo := (456543699121009493/200000000000000000)
  directionHi := (228271849560504746501/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree064.table
  base := (-3826110675130620346324174814153924207799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-334032826742404337500014216000000000000000)
      constant := (2546617121884632111254913277172915427635698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree064.table
  base := (-7652638144939744828955360746004722791927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-55681650201177795829476923187840000000000000)
      constant := (440433101580504131047571335044614510477683474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456543699121009493/200000000000000000)
  centralHi := (228271849560504746501/100000000000000000000)
  directionLo := (230076398191940731593/100000000000000000000)
  directionHi := (115038199095970365797/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree065.table
  base := (-3827172844431275522330536097400746454613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-339478424898335910953051091680000000000000)
      constant := (2642728922384702225213870629654726847447926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree065.table
  base := (-3827359984403242386070197907566338098111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-56588342294140402809407562988560000000000000)
      constant := (456900662262359367432690455191776816354389764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230076398191940731593/100000000000000000000)
  centralHi := (115038199095970365797/50000000000000000000)
  directionLo := (231866903002949572893/100000000000000000000)
  directionHi := (115933451501474786447/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree066.table
  base := (-7653368245260659576268356756838816417033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-344924023054267484406087967360000000000000)
      constant := (2740548595400138249359276408834897995565383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree066.table
  base := (-956713033550273456371372614131974738273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-6388337154122556643259800309920000000000000)
      constant := (52628784660508162750109337542444786246745712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231866903002949572893/100000000000000000000)
  centralHi := (115933451501474786447/50000000000000000000)
  directionLo := (46728737372791053397/20000000000000000000)
  directionHi := (116821843431977633493/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree067.table
  base := (-382464612769014119608839076467552590717/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-350369621210199057859124843040000000000000)
      constant := (2840075982370629094560508282181798461097340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree067.table
  base := (-7649593863508609964138633097792583720257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-58401726480065616769268842590000000000000000)
      constant := (490708278243718839915838820708742470428599934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46728737372791053397/20000000000000000000)
  centralHi := (116821843431977633493/50000000000000000000)
  directionLo := (29425882557544243811/12500000000000000000)
  directionHi := (235407060460353950489/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree068.table
  base := (-1528424120439165781289850404015953852033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-355815219366130631312161718720000000000000)
      constant := (2941310942030428699528483879816091306251915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree068.table
  base := (-7642391260266276748454944440030029236551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-59308418573028223749199482390720000000000000)
      constant := (508048291266052005185044385814881627920258162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29425882557544243811/12500000000000000000)
  centralHi := (235407060460353950489/100000000000000000000)
  directionLo := (237157322926759943677/100000000000000000000)
  directionHi := (118578661463379971839/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree069.table
  base := (-381592792782208364263294336523440427969/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-361260817522062204765198594400000000000000)
      constant := (3044253348452630524120377395167028380590380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree069.table
  base := (-3816049343778077092108958645187469868569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-6690567851776758969903346910160000000000000)
      constant := (58408787035412872335488354504589303151844284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237157322926759943677/100000000000000000000)
  centralHi := (118578661463379971839/50000000000000000000)
  directionLo := (119447381219713493281/50000000000000000000)
  directionHi := (238894762439426986563/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree070.table
  base := (-1904625076995698683358993465284939212333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-52386630811141968316890781440000000000000)
      constant := (449843298473802457900076243772021702054676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree070.table
  base := (-7618718129119445939200810797188971811803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-8731686108421919672722965998880000000000000)
      constant := (77657234093538957529158157681187705965415398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119447381219713493281/50000000000000000000)
  centralHi := (238894762439426986563/100000000000000000000)
  directionLo := (60154914192541769977/25000000000000000000)
  directionHi := (240619656770167079909/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree071.table
  base := (-1900514001278943702857984817941062777161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-372152013833925351671272345760000000000000)
      constant := (3255260064373089628605803946403551695676444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree071.table
  base := (-304090054076674992533023484907828069039/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-62028494851916044688991401792880000000000000)
      constant := (561812943248088342653399589852181519699210450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60154914192541769977/25000000000000000000)
  centralHi := (240619656770167079909/100000000000000000000)
  directionLo := (242332273804781870559/100000000000000000000)
  directionHi := (1514576711279886691/625000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree072.table
  base := (-1895631193587359195785807553515903156749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-377597611989856925124309221440000000000000)
      constant := (3363324184084037660105605199830882981277196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree072.table
  base := (-3791349965584767062654241933183103477881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-6992798549430961296546893510400000000000000)
      constant := (64479553843839748011478128303145005465017916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242332273804781870559/100000000000000000000)
  centralHi := (1514576711279886691/625000000000000000)
  directionLo := (15252054501796651253/6250000000000000000)
  directionHi := (244032872028746420049/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree073.table
  base := (-7559908248986560519623768193025157652337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-383043210145788498577346097120000000000000)
      constant := (3473095368417625086118295312941767275035487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree073.table
  base := (-3780032636235600044146429111003248767101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-63841879037841258648852681394320000000000000)
      constant := (599109751536577475473885828992252422573504524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15252054501796651253/6250000000000000000)
  centralHi := (244032872028746420049/100000000000000000000)
  directionLo := (245721700982638658371/100000000000000000000)
  directionHi := (61430425245659664593/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree074.table
  base := (-3767103945060363762913906858004253558763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-388488808301720072030382972800000000000000)
      constant := (3584573545780266412901115520875583151241226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree074.table
  base := (-3767174315658009530244517564822739950041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-64748571130803865628783321195040000000000000)
      constant := (618194234108035038973674053270074180553149084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245721700982638658371/100000000000000000000)
  centralHi := (61430425245659664593/25000000000000000000)
  directionLo := (247399001689586535657/100000000000000000000)
  directionHi := (123699500844793267829/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree075.table
  base := (-375271250297547607150714912282936188057/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-393934406457651645483419848480000000000000)
      constant := (3697758652070209937732378181962722535704140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree075.table
  base := (-7505551130344966491197803749276924980757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-7295029247085163623190440110640000000000000)
      constant := (70841047044156262165124240356637752166972326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247399001689586535657/100000000000000000000)
  centralHi := (123699500844793267829/50000000000000000000)
  directionLo := (4981300141136119047/2000000000000000000)
  directionHi := (249065007056805952351/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree076.table
  base := (-1494712153779992450250913622385803989739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-399380004613583218936456724160000000000000)
      constant := (3812650629838741994488587326035478022513945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree076.table
  base := (-467104610911172394172756137162545194283/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-66561955316729079588644600796480000000000000)
      constant := (657235311426836993987892071816699459964504736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4981300141136119047/2000000000000000000)
  centralHi := (249065007056805952351/100000000000000000000)
  directionLo := (250719942253123447389/100000000000000000000)
  directionHi := (25071994225312344739/10000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree077.table
  base := (-3719308115393502109768198199216442298927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-57832228967073541769927657120000000000000)
      constant := (561321346792388501584191724570969807815022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree077.table
  base := (-464919841554587738971490159346013003159/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-9638378201384526652653605799600000000000000)
      constant := (96741698720761705789394636244685940070683104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250719942253123447389/100000000000000000000)
  centralHi := (25071994225312344739/10000000000000000000)
  directionLo := (126182012532108071341/50000000000000000000)
  directionHi := (252364025064216142683/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree078.table
  base := (-1850148084069325497876169183826801302277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-410271200925446365842530475520000000000000)
      constant := (4047554998905546514296042631969946944753708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree078.table
  base := (-7400683009806816927253178974309429237861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-7597259944739365949833986710880000000000000)
      constant := (77493239537155524297212730270019083412206598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126182012532108071341/50000000000000000000)
  centralHi := (252364025064216142683/100000000000000000000)
  directionLo := (31749683278394455209/12500000000000000000)
  directionHi := (253997466227155641673/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree079.table
  base := (-7359489934804866012452520161293357336887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-415716799081377939295567351200000000000000)
      constant := (4167567302292956492289326565056625490492537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree079.table
  base := (-7359571136180406082213606385137460827473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-69282031595616900528436520198640000000000000)
      constant := (717977100024690748045564369571878835951519326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31749683278394455209/12500000000000000000)
  centralHi := (253997466227155641673/100000000000000000000)
  directionLo := (6390511743642768909/2500000000000000000)
  directionHi := (255620469745710756361/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree080.table
  base := (-7315309791142838337986416601494119497773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-421162397237309512748604226880000000000000)
      constant := (4289286300235065484344475864926788144609123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree080.table
  base := (-7315382498297954506774054218630860147691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-70188723688579507508367159999360000000000000)
      constant := (738805718422341597450458043270108232147628842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6390511743642768909/2500000000000000000)
  centralHi := (255620469745710756361/100000000000000000000)
  directionLo := (2572332331877445913/1000000000000000000)
  directionHi := (257233233187744591301/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree081.table
  base := (-7268052594775636104091157181888608178857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-426607995393241086201641102560000000000000)
      constant := (4412711958947137050798235766407458199236007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree081.table
  base := (-726811768616503738237281622316982091197/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-7899490642393568276477533311120000000000000)
      constant := (84436111815987556788815379750024217955642460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2572332331877445913/1000000000000000000)
  centralHi := (257233233187744591301/100000000000000000000)
  directionLo := (129417973982966661521/50000000000000000000)
  directionHi := (258835947965933323043/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree082.table
  base := (-3608859484104758659066946655168864854189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-432053593549172659654677978240000000000000)
      constant := (4537844247926364549289615850513451244289478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree082.table
  base := (-902222154091925272923113088505413635709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-72002107874504721468228439600800000000000000)
      constant := (781334959558743141540616645301072212477935664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129417973982966661521/50000000000000000000)
  centralHi := (258835947965933323043/100000000000000000000)
  directionLo := (130214399801467905921/50000000000000000000)
  directionHi := (260428799602935811843/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree083.table
  base := (-7164309474342576686174633054889708149599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-437499191705104233107714853920000000000000)
      constant := (4664683139590741339221675721910404300669649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree083.table
  base := (-3582180810157948034897758110168738995121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-72908799967467328448159079401520000000000000)
      constant := (803035574238355236018330235731901099713459004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130214399801467905921/50000000000000000000)
  centralHi := (260428799602935811843/100000000000000000000)
  directionLo := (262011967982053936913/100000000000000000000)
  directionHi := (131005983991026968457/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree084.table
  base := (-710782462300135191049096292789809348589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-63277827123005115222964532800000000000000)
      constant := (684746944136966724740401948784713345598770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree084.table
  base := (-111060488847319176776871876367435101539/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1691)
      previous := (703)
      next := (0)
      square := (24505191701692080538665940560000000000000)
      linear := (-1171674477149681514731582844480000000000000)
      constant := (13095664236686714074102049740973003341189504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262011967982053936913/100000000000000000000)
  centralHi := (131005983991026968457/50000000000000000000)
  directionLo := (263585627584342342313/100000000000000000000)
  directionHi := (131792813792171171157/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree085.table
  base := (-881033109592372093669713257112176574979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-448390388016967380013788605280000000000000)
      constant := (4923480633365338197017563276012026782608232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree085.table
  base := (-7048306627815890218084746647915643155729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-74722184153392542408020359002960000000000000)
      constant := (847308774423358498514278889843545624629823198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263585627584342342313/100000000000000000000)
  centralHi := (131792813792171171157/50000000000000000000)
  directionLo := (33143743464131538303/12500000000000000000)
  directionHi := (10605997908522092257/4000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree086.table
  base := (-6985630655978974227619943459776107461749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-453835986172898953466825480960000000000000)
      constant := (5055439192209702082508515655590970734374299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree086.table
  base := (-3492834003434391802632383840723577224253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-75628876246355149387950998803680000000000000)
      constant := (869881353902748791903871423509712487987759372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33143743464131538303/12500000000000000000)
  centralHi := (10605997908522092257/4000000000000000000)
  directionLo := (266705092706226982799/100000000000000000000)
  directionHi := (666762731765567457/250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree087.table
  base := (-6919922343579180893964968785477425148421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-459281584328830526919862356640000000000000)
      constant := (5189104266731824738769993391431606167727371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree087.table
  base := (-6919955753540251836355042680611768563981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-8503952037701972929764626511600000000000000)
      constant := (99193842525408689655425911096480420126568758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266705092706226982799/100000000000000000000)
  centralHi := (666762731765567457/250000000000000000)
  directionLo := (268251222138203662383/100000000000000000000)
  directionHi := (16765701383637728899/6250000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree088.table
  base := (-3425570144440894347369305390980232286063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-464727182484762100372899232320000000000000)
      constant := (5324475839813938760431050874883937235965826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree088.table
  base := (-1370234033961866697665705812979462611909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-77442260432280363347812278405120000000000000)
      constant := (915898458504037135275152882923485128933331790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268251222138203662383/100000000000000000000)
  centralHi := (16765701383637728899/6250000000000000000)
  directionLo := (53957698202144481017/20000000000000000000)
  directionHi := (134894245505361202543/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree089.table
  base := (-6779284811307959031333156651477745820711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-470172780640693673825936108000000000000000)
      constant := (5461553895804407238823466033037590454785161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree089.table
  base := (-6779311532545191923578140505988139957489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-78348952525242970327742918205840000000000000)
      constant := (939342979031038158262155523949366145017452318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53957698202144481017/20000000000000000000)
  centralHi := (134894245505361202543/50000000000000000000)
  directionLo := (33914631241786109021/12500000000000000000)
  directionHi := (271317049934288872169/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree090.table
  base := (-670435620354879253021429625963404605173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-475618378796625247278972983680000000000000)
      constant := (5600338420361366243250420062477931743465230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree090.table
  base := (-6704380096218914350471080904245694486507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-8806182735356175256408173111840000000000000)
      constant := (107008682476632198399980250931655297462900826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33914631241786109021/12500000000000000000)
  centralHi := (271317049934288872169/100000000000000000000)
  directionLo := (136418522650196002087/50000000000000000000)
  directionHi := (10913481812015680167/4000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree091.table
  base := (-828294341799816177835223902425414323603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-68723425278936688676001408480000000000000)
      constant := (820118485759128286054032092024176797878232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree091.table
  base := (-6626376095304004831228296130377093469001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-11451762387309740612514885401040000000000000)
      constant := (141014849488391620291749031129772376006152866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136418522650196002087/50000000000000000000)
  centralHi := (10913481812015680167/4000000000000000000)
  directionLo := (34293577430641740521/12500000000000000000)
  directionHi := (274348619445133924169/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree092.table
  base := (-1636320162817655490589762101402016780099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-486509575108488394185046735040000000000000)
      constant := (5883026823538743355779332841245204711100596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree092.table
  base := (-3272649873200938336473684355311511252527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-81069028804130791267534837608000000000000000)
      constant := (1011420389698810808757677792426594447354881348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34293577430641740521/12500000000000000000)
  centralHi := (274348619445133924169/100000000000000000000)
  directionLo := (68962977701197434431/25000000000000000000)
  directionHi := (11034076432191589509/4000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree093.table
  base := (-1292226836486536953223403850617079523859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-491955173264419967638083610720000000000000)
      constant := (6026930678850789187227068033398815516654545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree093.table
  base := (-403821953132774713265247921664877268351/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-9108413433010377583051719712080000000000000)
      constant := (115114163393049021901830089838725251989030688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68962977701197434431/25000000000000000000)
  centralHi := (11034076432191589509/4000000000000000000)
  directionLo := (277347054063778421387/100000000000000000000)
  directionHi := (69336763515944605347/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree094.table
  base := (-3186957769496111482828952030589831232147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-497400771420351541091120486400000000000000)
      constant := (6172540955905767745268022405962196539249594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree094.table
  base := (-6373930792761768707110022799412295207229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-82882412990056005227396117209440000000000000)
      constant := (1060925187455860838729482305605065200645016198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277347054063778421387/100000000000000000000)
  centralHi := (69336763515944605347/25000000000000000000)
  directionLo := (69708545073873111519/25000000000000000000)
  directionHi := (278834180295492446077/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree095.table
  base := (-6283624916661401052480279557184992310943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-502846369576283114544157362080000000000000)
      constant := (6319857645113782969818765699297935376763793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree095.table
  base := (-6283638547760765229401772252385845701821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-83789105083018612207326757010160000000000000)
      constant := (1086113539077249283879517487122461156818944902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69708545073873111519/25000000000000000000)
  centralHi := (278834180295492446077/100000000000000000000)
  directionLo := (280313417096402906379/100000000000000000000)
  directionHi := (14015670854820145319/5000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree096.table
  base := (-6190262497325893671374375788386309578217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-508291967732214687997194237760000000000000)
      constant := (6468880737562436803284576641089070830667367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree096.table
  base := (-309513733851765967532109875237124902711/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-9410644130664579909695266312320000000000000)
      constant := (123510280457370413502825213201777116716177960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280313417096402906379/100000000000000000000)
  centralHi := (14015670854820145319/5000000000000000000)
  directionLo := (281784888713828482543/100000000000000000000)
  directionHi := (17611555544614280159/6250000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree097.table
  base := (-761728556305000735820488743218110459391/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-513737565888146261450231113440000000000000)
      constant := (6619610224948468297518493088978500699918728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree097.table
  base := (-6093839332128996358195849772588724334369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-85602489268943826167188036611600000000000000)
      constant := (1137362141370161330416110793132210706233778878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281784888713828482543/100000000000000000000)
  centralHi := (17611555544614280159/6250000000000000000)
  directionLo := (283248716167730334581/100000000000000000000)
  directionHi := (141624358083865167291/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree098.table
  base := (-5994322934267722561974432436057096851813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-74169023434868262129038284160000000000000)
      constant := (967435157073848884884023296147600322037309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree098.table
  base := (-1498583163811628455189106659452376459573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-12358454480272347592445525201760000000000000)
      constant := (166203198529987294641611219809444020379376872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283248716167730334581/100000000000000000000)
  centralHi := (141624358083865167291/50000000000000000000)
  directionLo := (28470501736687082339/10000000000000000000)
  directionHi := (284705017366870823391/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree099.table
  base := (-5891746096987107224690289206915887456489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-524628762200009408356304864800000000000000)
      constant := (6926188354007133380466453641821121514632039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree099.table
  base := (-294587739008475148493880792446265808521/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-9712874828318782236338812912560000000000000)
      constant := (132197029785958258781650775785547871137689560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28470501736687082339/10000000000000000000)
  centralHi := (284705017366870823391/100000000000000000000)
  directionLo := (286153907219651597181/100000000000000000000)
  directionHi := (143076953609825798591/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree100.table
  base := (-5786098077673487138709470615913170052509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-530074360355940981809341740480000000000000)
      constant := (7082036981604350820417463267820254667427059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree100.table
  base := (-5786105833069918185020189757465509353867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-88322565547831647106979956013760000000000000)
      constant := (1216414775459748156182686512417238786749003754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286153907219651597181/100000000000000000000)
  centralHi := (143076953609825798591/50000000000000000000)
  directionLo := (71898874434981478623/25000000000000000000)
  directionHi := (287595497739925914493/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree101.table
  base := (-5677379007175104096046506594150498213877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-535519958511872555262378616160000000000000)
      constant := (7239591975897030666232479984406625587520027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree101.table
  base := (-2838692966616467579076545648506128184921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-89229257640794254086910595814480000000000000)
      constant := (1243346910921396819291917660701256708936194204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71898874434981478623/25000000000000000000)
  centralHi := (287595497739925914493/100000000000000000000)
  directionLo := (289029898148060954383/100000000000000000000)
  directionHi := (18064368634253809649/6250000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree102.table
  base := (-5565589008893353764695464998240814954479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-540965556667804128715415491840000000000000)
      constant := (7398853330838504530179794466606200067230529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree102.table
  base := (-2782797596849897309641344175007900586853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-10015105525972984562982359512800000000000000)
      constant := (141174408173472105494195542074566063364791308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289029898148060954383/100000000000000000000)
  centralHi := (18064368634253809649/6250000000000000000)
  directionLo := (145228607483754080119/50000000000000000000)
  directionHi := (290457214967508160239/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree103.table
  base := (-2725364099739178702951715254051022888591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-546411154823735702168452367520000000000000)
      constant := (7559821040712916470458299565102999756918082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree103.table
  base := (-681341715229978380906932739355008180141/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-91042641826719468046771875415920000000000000)
      constant := (1298083062527006801309129800161739560528325936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145228607483754080119/50000000000000000000)
  centralHi := (290457214967508160239/100000000000000000000)
  directionLo := (29187755211712325813/10000000000000000000)
  directionHi := (291877552117123258131/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree104.table
  base := (-5332796689449388093512467605196081450781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-551856752979667275621489243200000000000000)
      constant := (7722495100104822106449734120305392008911731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree104.table
  base := (-5332801619859815526042632275132034110489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-91949333919682075026702515216640000000000000)
      constant := (1325887077007352930755463878561601913230938318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29187755211712325813/10000000000000000000)
  centralHi := (291877552117123258131/100000000000000000000)
  directionLo := (146645505499731188541/50000000000000000000)
  directionHi := (293291010999462377083/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree105.table
  base := (-5211794583748591262016521116796059489193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-79614621590799835582075159840000000000000)
      constant := (1126696500553150901694842119382427583575649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree105.table
  base := (-5211798985257902027288022346305317790317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1691)
      previous := (703)
      next := (0)
      square := (24505191701692080538665940560000000000000)
      linear := (-1473905174803883841375129444720000000000000)
      constant := (21491773273465826774854816628065529958420058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146645505499731188541/50000000000000000000)
  centralHi := (293291010999462377083/100000000000000000000)
  directionLo := (920930283078958061/312500000000000000)
  directionHi := (294697690585266579521/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree106.table
  base := (-5087721982235480557967653230911189246463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-562747949291530422527562994560000000000000)
      constant := (8052962247121502918019730664005351726923313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree106.table
  base := (-5087725911228402071031028345241832713329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-93762718105607288986563794818080000000000000)
      constant := (1382366979450212792892225780011710331921594398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (920930283078958061/312500000000000000)
  centralHi := (294697690585266579521/100000000000000000000)
  directionLo := (29609768749433399737/10000000000000000000)
  directionHi := (296097687494333997371/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree107.table
  base := (-124014474503221011779843925830179631487/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-568193547447461995980599870240000000000000)
      constant := (8220755325187441484915674844092847922285480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree107.table
  base := (-4960582487023150845999602279639739518313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-94669410198569895966494434618800000000000000)
      constant := (1411042865964468981256458392855239747703631406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29609768749433399737/10000000000000000000)
  centralHi := (296097687494333997371/100000000000000000000)
  directionLo := (297491096072966582183/100000000000000000000)
  directionHi := (37186387009120822773/12500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree108.table
  base := (-4830365668401914588949273637336891916377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-573639145603393569433636745920000000000000)
      constant := (8390254733612183076776259761370492296097527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree108.table
  base := (-4830368798274348903845771084479807149369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-10619566921281389216269452713280000000000000)
      constant := (160001041676818582658837499587648810094256542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297491096072966582183/100000000000000000000)
  centralHi := (37186387009120822773/12500000000000000000)
  directionLo := (14943900423408357141/5000000000000000000)
  directionHi := (298878008468167142821/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree109.table
  base := (-2348541067068045742984045697932979564041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-579084743759325142886673621600000000000000)
      constant := (8561460468128739653439524886562568002723982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree109.table
  base := (-4697084927283297280389472060913408341937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-96482794384495109926355714220240000000000000)
      constant := (1469266506177599853289124428015969364581704094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14943900423408357141/5000000000000000000)
  centralHi := (298878008468167142821/100000000000000000000)
  directionLo := (300258514698751794867/100000000000000000000)
  directionHi := (75064628674687948717/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree110.table
  base := (-4560728460837709438413989921348000911873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-584530341915256716339710497280000000000000)
      constant := (8734372524645300639373445018653947955318223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree110.table
  base := (-4560730953278901340679622069615516598253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-97389486477457716906286354020960000000000000)
      constant := (1498814258594247758547460885996592029243067686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300258514698751794867/100000000000000000000)
  centralHi := (75064628674687948717/25000000000000000000)
  directionLo := (301632702723533120831/100000000000000000000)
  directionHi := (4713010980055205013/1562500000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree111.table
  base := (-4421304728722077651741039510652817263939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-589975940071188289792747372960000000000000)
      constant := (8908990899231315883510770713098011954066989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree111.table
  base := (-2210653476324685924970919094541535273451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-10921797618935591542912999313520000000000000)
      constant := (169850292414993482516687324651288731777632436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301632702723533120831/100000000000000000000)
  centralHi := (4713010980055205013/1562500000000000000)
  directionLo := (75750164626680045869/25000000000000000000)
  directionHi := (303000658506720183477/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree112.table
  base := (-4278811014968347834707955973580127657601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-85060219746731409035112035520000000000000)
      constant := (1297902226872143850303189270744939106396793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree112.table
  base := (-4278812999150153728283322022633658201249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-14171838666197561552306804803200000000000000)
      constant := (222683089287744269117355509897693431599783634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75750164626680045869/25000000000000000000)
  centralHi := (303000658506720183477/100000000000000000000)
  directionLo := (304362466080672995333/100000000000000000000)
  directionHi := (152181233040336497667/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree113.table
  base := (-826649478789691785141194218074247065159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-600867136383051436698821124320000000000000)
      constant := (9263346587622148837226937207771809469036045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree113.table
  base := (-4133249164090761465564473578979641502481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-100109562756345537846078273423120000000000000)
      constant := (1589201237865998456040856972994199605753305822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304362466080672995333/100000000000000000000)
  centralHi := (152181233040336497667/50000000000000000000)
  directionLo := (38214775950767634841/12500000000000000000)
  directionHi := (305718207606141078729/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree114.table
  base := (-3984613937433013552487555363164374423133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-606312734538983010151858000000000000000000)
      constant := (9443083894265982010064736596164945653266483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree114.table
  base := (-1992307758251444896401864554255353079877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-11224028316589793869556545913760000000000000)
      constant := (179990163304703718503718531781893557167096972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38214775950767634841/12500000000000000000)
  centralHi := (305718207606141078729/100000000000000000000)
  directionLo := (307067963430108309697/100000000000000000000)
  directionHi := (153533981715054154849/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree115.table
  base := (-3832910714776622040716653773247809842487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-611758332694914583604894875680000000000000)
      constant := (9624527504638130564678189756310857317718137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree115.table
  base := (-239557007705743381737663562379108138529/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-101922946942270751805939553024560000000000000)
      constant := (1650912320112120204151569476077654233541708768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307067963430108309697/100000000000000000000)
  centralHi := (153533981715054154849/50000000000000000000)
  directionLo := (308411812141359286749/100000000000000000000)
  directionHi := (1233647248565437147/400000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree116.table
  base := (-3678137793084963748934667885370284399759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-617203930850846157057931751360000000000000)
      constant := (9807677415450416212498768011536856064411809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree116.table
  base := (-3678139049373493080986613555931230324123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-102829639035233358785870192825280000000000000)
      constant := (1682203788460057694089327612180857893687111626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308411812141359286749/100000000000000000000)
  centralHi := (1233647248565437147/400000000000000000)
  directionLo := (61949966124775193093/20000000000000000000)
  directionHi := (154874915311937982733/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree117.table
  base := (-352029523736556200667780826535353879659/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-622649529006777730510968627040000000000000)
      constant := (9992533623517470310379197044117676598967090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree117.table
  base := (-3520296357797332067990174967805594569893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-11526259014243996196200092514000000000000000)
      constant := (190420652698406427945968320127175465589354374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61949966124775193093/20000000000000000000)
  centralHi := (154874915311937982733/50000000000000000000)
  directionLo := (31108209410816721933/10000000000000000000)
  directionHi := (311082094108167219331/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree118.table
  base := (-3359383110664044256325992762763096452347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-628095127162709303964005502720000000000000)
      constant := (10179096125750057113642860879424608273834997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree118.table
  base := (-839846027464714278537460246158354301901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-104643023221158572745731472426720000000000000)
      constant := (1745658577102357425716849830425819934206039448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31108209410816721933/10000000000000000000)
  centralHi := (311082094108167219331/100000000000000000000)
  directionLo := (312408676220628295649/100000000000000000000)
  directionHi := (6248173524412565913/2000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree119.table
  base := (-3195401474187459859537434065779449810187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-90505817902662982488148911200000000000000)
      constant := (1481052131307004457652643870819543851328691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree119.table
  base := (-1597701182600391263828262020923511906967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11340000000000000000000000000000000000000000
      center := (15219)
      previous := (6327)
      next := (0)
      square := (220546725315228724847993465040000000000000)
      linear := (-15078530759160168532237444603920000000000000)
      constant := (253974556633816078645758999587445474994998844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312408676220628295649/100000000000000000000)
  centralHi := (6248173524412565913/2000000000000000000)
  directionLo := (313729649031021804747/100000000000000000000)
  directionHi := (78432412257755451187/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree120.table
  base := (-151417519370802575667539859769295558329/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-638986323474572450870079254080000000000000)
      constant := (10557340000799860688001241107026090352837580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree120.table
  base := (-605670236381057528211093202588896179907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-11828489711898198522843639114240000000000000)
      constant := (201141759091962987375817805690182967846610130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313729649031021804747/100000000000000000000)
  centralHi := (78432412257755451187/25000000000000000000)
  directionLo := (157522541549083442717/50000000000000000000)
  directionHi := (63009016619633377087/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree121.table
  base := (-285822990820471974898290494270112140473/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-644431921630504024323116129760000000000000)
      constant := (10749021367867655440911438596527645051168230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree121.table
  base := (-714557654144487049014834041422194681063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-107363099500046393685523391828880000000000000)
      constant := (1843020382825885373065276424076902474486887624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157522541549083442717/50000000000000000000)
  centralHi := (63009016619633377087/20000000000000000000)
  directionLo := (316355047513918505941/100000000000000000000)
  directionHi := (158177523756959252971/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree122.table
  base := (-671260023218820318230298365763090281341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-649877519786435597776153005440000000000000)
      constant := (10942409017592646443681215192630434304857164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree122.table
  base := (-2685040724424292763168764430070741322941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-108269791593009000665454031629600000000000000)
      constant := (1876055548993146524776427515323618455378494342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316355047513918505941/100000000000000000000)
  centralHi := (158177523756959252971/50000000000000000000)
  directionLo := (79414902486378616399/25000000000000000000)
  directionHi := (317659609945514465597/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree123.table
  base := (-78399406134390591578634311819060517217/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-655323117942367171229189881120000000000000)
      constant := (11137502947286068316888389769467713109003744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree123.table
  base := (-250878155931977296983567607972230006861/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-12130720409552400849487185714480000000000000)
      constant := (212153481100198556277455571347744931339485980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79414902486378616399/25000000000000000000)
  centralHi := (317659609945514465597/100000000000000000000)
  directionLo := (318958836676363538091/100000000000000000000)
  directionHi := (79739709169090884523/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree124.table
  base := (-1164726335990376016927131204190974812661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-660768716098298744682226756800000000000000)
      constant := (11334303154326402474240746174949284468359222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree124.table
  base := (-582363293468461622997990677853316822059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-110083175778934214625315311231040000000000000)
      constant := (1942997725134192943195746949000001484265982632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318958836676363538091/100000000000000000000)
  centralHi := (79739709169090884523/25000000000000000000)
  directionLo := (320252792645344323811/100000000000000000000)
  directionHi := (80063198161336080953/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree125.table
  base := (-2147055172114119109650402837796238326179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-666214314254230318135263632480000000000000)
      constant := (11532809636155943067929233920947984322017229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree125.table
  base := (-2147055619488792380423109545578132271107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-110989867871896821605245951031760000000000000)
      constant := (1976904734282333043767232754254700786031952634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320252792645344323811/100000000000000000000)
  centralHi := (80063198161336080953/25000000000000000000)
  directionLo := (160770770742340369563/50000000000000000000)
  directionHi := (321541541484680739127/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree126.table
  base := (-980794273830279691089912401579706898957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (95)
      previous := (38)
      next := (0)
      square := (1361399538982893363259218920000000000000)
      linear := (-95951416058594555941185786880000000000000)
      constant := (1676146055753950299423481833737884103414602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree126.table
  base := (-392317789282761624965540712701344346891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1260000000000000000000000000000000000000000
      center := (1691)
      previous := (703)
      next := (0)
      square := (24505191701692080538665940560000000000000)
      linear := (-1776135872458086168018676044960000000000000)
      constant := (31922259634084590135529050387878153061458670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160770770742340369563/50000000000000000000)
  centralHi := (321541541484680739127/100000000000000000000)
  directionLo := (161412572778228324459/50000000000000000000)
  directionHi := (322825145556456648919/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree127.table
  base := (-443263212100200816086214394510149554141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-677105510566093465041337383840000000000000)
      constant := (11934941414252273768113948786196010687388364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree127.table
  base := (-1773053203794875826760722193060889931513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-112803252057822035565107230633200000000000000)
      constant := (2045590592739060541586895798722502655723649806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161412572778228324459/50000000000000000000)
  centralHi := (322825145556456648919/100000000000000000000)
  directionLo := (324103665987828930287/100000000000000000000)
  directionHi := (20256479124239308143/6250000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree128.table
  base := (-1581448122990494682626719913253352435573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-682551108722025038494374259520000000000000)
      constant := (12138566705695681531980382052250585730656923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree128.table
  base := (-96523952619679565836517786679420841/610351562500000000000000000000000000)
  polynomial :=
    { denominator := 79380000000000000000000000000000000000000000
      center := (106533)
      previous := (44289)
      next := (0)
      square := (1543827077206601073935954255280000000000000)
      linear := (-113709944150784642545037870433920000000000000)
      constant := (2080369441275797964489650378454446200654102528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell005.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324103665987828930287/100000000000000000000)
  centralHi := (20256479124239308143/6250000000000000000)
  directionLo := (325377162704995226731/100000000000000000000)
  directionHi := (81344290676248806683/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 2
  qDenominator := 7
  table := BinomialMassData.Q2_7.Degree129.table
  base := (-693387209505034115360492012724471568463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (665)
      previous := (266)
      next := (0)
      square := (9529796772880253542814532440000000000000)
      linear := (-687996706877956611947411135200000000000000)
      constant := (12343898262276434092472589595713001786290626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2_7.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 37
  qDenominator := 126
  table := BinomialMassData.Q37_126.Degree129.table
  base := (-1386774701266011070135335817079144960067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8820000000000000000000000000000000000000000
      center := (11837)
      previous := (4921)
      next := (0)
      square := (171536341911844563770661583920000000000000)
      linear := (-12735181804860805502774278914960000000000000)
      constant := (235048766909318370345221609347236194145220906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q37_126.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell005.Kernel129
