import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell026.Parameters
import ForestUnimodality.BinomialMassData.Q4_9.Batch000_049
import ForestUnimodality.BinomialMassData.Q4_9.Batch050_099
import ForestUnimodality.BinomialMassData.Q4_9.Batch100_149
import ForestUnimodality.BinomialMassData.Q301_666.Batch000_049
import ForestUnimodality.BinomialMassData.Q301_666.Batch050_099
import ForestUnimodality.BinomialMassData.Q301_666.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree000.table
  base := (3030664666877651807318727637/100000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (7709130293725021537687425075000000000000)
      constant := (681899550047471656646713718325000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree000.table
  base := (3030664666877651807318727637/100000000000000000000000000)
  polynomial :=
    { denominator := 1665000000000000000000000000000000000000000
      center := (6205)
      previous := (5117)
      next := (0)
      square := (138974305289755770062565254550000000000000)
      linear := (570475641735651593788869455550000000000000)
      constant := (50460566703512902591856815156050000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree001.table
  base := (186955142754592067471664456329636747107467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (217431693692044226140502868300000000000000)
      constant := (15033375366618369687094320924700576515704827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree001.table
  base := (185006243862667004318374008451258368729089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (296274245611510987885722774157200000000000000)
      constant := (20362349929797458664267020723979214249999950121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24845199749997663293/50000000000000000000)
  directionHi := (49690399499995326587/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree002.table
  base := (29830648507740588042731359728189542864937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (39333674202496919231064608475000000000000)
      constant := (2367964374973200025652239500583352972059897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree002.table
  base := (117076457317178530416871733639881984461939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (212611713827078014308058490918100000000000000)
      constant := (12714687828210181208484770287144473374999953771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24845199749997663293/50000000000000000000)
  centralHi := (49690399499995326587/100000000000000000000)
  directionLo := (35136418446315325911/50000000000000000000)
  directionHi := (70272836892630651823/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree003.table
  base := (19798913986345989136938181128122511057689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (2701047220220309103000388875000000000000)
      constant := (171250107534483681805318420853102599519201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree003.table
  base := (77220316457689099709038648816019227458907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (14327686893627226747821578631000000000000000)
      constant := (913099518626985373075543630303497901521193147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/50000000000000000000)
  centralHi := (70272836892630651823/100000000000000000000)
  directionLo := (21516574145596760473/25000000000000000000)
  directionHi := (86066296582387041893/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree004.table
  base := (684310767410137679094730350804137648971/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (9285175761468644622942391275000000000000)
      constant := (1038656911288872961500459419902702991333020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree004.table
  base := (53163039387232897582673517147965865853911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (45286650258212067152729924439900000000000000)
      constant := (5510835158322877895320004929709386898674336879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21516574145596760473/25000000000000000000)
  centralHi := (86066296582387041893/100000000000000000000)
  directionLo := (99380798999990653173/100000000000000000000)
  directionHi := (49690399499995326587/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree005.table
  base := (19649177330723255021961181441966674718203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-11478146918090985362237434650000000000000)
      constant := (1450154254489739876427593233799300652174443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree005.table
  base := (19036089456851637039694215479796675925593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-19187940763110453212467179399600000000000000)
      constant := (1917931531782347757084715181889986096713082177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99380798999990653173/100000000000000000000)
  centralHi := (49690399499995326587/50000000000000000000)
  directionLo := (111111111111111111111/100000000000000000000)
  directionHi := (13888888888888888889/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree006.table
  base := (14551488705335624085001874309848165143367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (170)
      previous := (136)
      next := (0)
      square := (3756062305128534326015277150000000000000)
      linear := (-4614071706568806663373294650000000000000)
      constant := (116557813173512301549014794788633486290303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree006.table
  base := (7038333271516299983498614496807390316627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-6779911850591882222366591224350000000000000)
      constant := (154012330301110991891146303619827712182322534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/100000000000000000000)
  centralHi := (13888888888888888889/12500000000000000000)
  directionLo := (121716123890036914101/100000000000000000000)
  directionHi := (60858061945018457051/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree007.table
  base := (4405940357818193903805524169819467727051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-143150287600295069156963738100000000000000)
      constant := (1575372773623781876952685077176884429455655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree007.table
  base := (42561968379161529525693379801065546663/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-102850472547543426790131462638700000000000000)
      constant := (1042107635009606385200806996998451850978351750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121716123890036914101/100000000000000000000)
  centralHi := (60858061945018457051/50000000000000000000)
  directionLo := (131468439624435912057/100000000000000000000)
  directionHi := (65734219812217956029/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree008.table
  base := (3372643640511904576087344108862660775837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-203247284482351618373208172500000000000000)
      constant := (1233864841355322852011304799289377614213985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree008.table
  base := (8128127697289691306640293099971278481517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-144681738439759913578963604258250000000000000)
      constant := (819450392298499328773676859422115099536938613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/100000000000000000000)
  centralHi := (65734219812217956029/50000000000000000000)
  directionLo := (35136418446315325911/25000000000000000000)
  directionHi := (28109134757052260729/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree009.table
  base := (12903089952034949553046008305910607450299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-29260475707156463065494734100000000000000)
      constant := (112975718632827299806904142353195467052691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree009.table
  base := (774732631816456121095156418500227574449/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-20723667147997377818643971764200000000000000)
      constant := (75583012198406466696710056065242931558289032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/25000000000000000000)
  centralHi := (28109134757052260729/20000000000000000000)
  directionLo := (1863389981249824747/1250000000000000000)
  directionHi := (149071198499985979761/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree010.table
  base := (4869942332359483799718055896034446157423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-161720639123232358402848520650000000000000)
      constant := (445479315223744789387106681578790138751263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree010.table
  base := (4651825537776044963221598695137806873527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-228344270224192887156627887497350000000000000)
      constant := (602556554876709808139181674511136266398535503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1863389981249824747/1250000000000000000)
  centralHi := (149071198499985979761/100000000000000000000)
  directionLo := (39283710065919306911/25000000000000000000)
  directionHi := (31426968052735445529/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree011.table
  base := (7129427864181167612300072225091658669719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-383538275128521266021941475700000000000000)
      constant := (836618197020591331555669384232424352247239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree011.table
  base := (6745735187717606683783655512120281530371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-540351072232818747890920058233800000000000000)
      constant := (1146775374429685869135834849486630898621309819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39283710065919306911/25000000000000000000)
  centralHi := (31426968052735445529/20000000000000000000)
  directionLo := (82402205412174032763/50000000000000000000)
  directionHi := (164804410824348065527/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree012.table
  base := (196882907916013305238621368080322704549/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-49292808001175312804242878900000000000000)
      constant := (93515419151170264754671617418072608523525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree012.table
  base := (4578984095817275256137167670331741587221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-69334844890805746829842704608100000000000000)
      constant := (129958328523056776320319879209557388096149941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82402205412174032763/50000000000000000000)
  centralHi := (164804410824348065527/100000000000000000000)
  directionLo := (34426518632954816757/20000000000000000000)
  directionHi := (86066296582387041893/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree013.table
  base := (94463295837905780139284644754730991359/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-125933067223158591113607586125000000000000)
      constant := (224581466710792759878583091101065682400632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree013.table
  base := (1356347868163300226387463382658254114277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-353838067900842347523124312356000000000000000)
      constant := (631801997732363611157384424376803640478062253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34426518632954816757/20000000000000000000)
  centralHi := (86066296582387041893/50000000000000000000)
  directionLo := (22395160411940415701/12500000000000000000)
  directionHi := (179161283295523325609/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree014.table
  base := (136878731725894669974697133324145967851/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-281914632887345456835337389450000000000000)
      constant := (500792336661016445383639524196279116979655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree014.table
  base := (543321388184986558891787540737326613271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-395669333793058834311956453975550000000000000)
      constant := (711016970993045575870714166682121410819007919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22395160411940415701/12500000000000000000)
  centralHi := (179161283295523325609/100000000000000000000)
  directionLo := (11620278146306604833/6250000000000000000)
  directionHi := (185924450340905677329/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree015.table
  base := (-41838107115483462210878811897582674067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (170)
      previous := (136)
      next := (0)
      square := (3756062305128534326015277150000000000000)
      linear := (-34662570147597081271495511850000000000000)
      constant := (63771155569784109493837629692921755933397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree015.table
  base := (-170597308391890871599288690872914026467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-48611177742808369011198732843900000000000000)
      constant := (91125292168881972845171329124817326279900093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11620278146306604833/6250000000000000000)
  centralHi := (185924450340905677329/100000000000000000000)
  directionLo := (48112522432468813709/25000000000000000000)
  directionHi := (192450089729875254837/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree016.table
  base := (-1366291743757490317563185538716738921227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-684023259538804012103163647700000000000000)
      constant := (1334644391741254792709084531363944147380613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree016.table
  base := (-800796039062510738451285302823502109571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-479331865577491807889620737214650000000000000)
      constant := (957427633618817282454038664457204674571781381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48112522432468813709/25000000000000000000)
  centralHi := (192450089729875254837/100000000000000000000)
  directionLo := (198761597999981306347/100000000000000000000)
  directionHi := (49690399499995326587/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree017.table
  base := (-2503146479656556775891717693727346168369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-744120256420860561319408082100000000000000)
      constant := (1559924383902244759233933811208084960362111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree017.table
  base := (-543617730651051104002809111225844973547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-1042326262939416589356905757668400000000000000)
      constant := (2243223745351662532901774506299611383641733585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198761597999981306347/100000000000000000000)
  centralHi := (49690399499995326587/25000000000000000000)
  directionLo := (102439382858809859/50000000000000000)
  directionHi := (204878765717619718001/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree018.table
  base := (-140528305469314231395475619217396057203/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-89357472589213012281739168500000000000000)
      constant := (202464936926656002459975858476085887129325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree018.table
  base := (-3709339649441161229388315409420797466637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-125109866080427729214952226767500000000000000)
      constant := (291476891668273869974427403733726354413565523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102439382858809859/50000000000000000)
  centralHi := (204878765717619718001/100000000000000000000)
  directionLo := (105409255338945977733/50000000000000000000)
  directionHi := (210818510677891955467/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree019.table
  base := (-1102961325775574323456142427220891500343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-216078562546243414937974237725000000000000)
      constant := (530044889979210968883821536495107788472217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree019.table
  base := (-1147634119198565139165465812358527680063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-604825663254141268256117162073300000000000000)
      constant := (1526687772975092448908637869067112948170987986) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105409255338945977733/50000000000000000000)
  centralHi := (210818510677891955467/100000000000000000000)
  directionLo := (108297714942321821187/50000000000000000000)
  directionHi := (1732763439077149139/800000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree020.table
  base := (-2605891196993562722163276959507317459081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-462205623533515104484070692650000000000000)
      constant := (1226439605250031271974539194279907285814439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree020.table
  base := (-1074858958127280908658914910241554252889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-1293313858292715510089898607385700000000000000)
      constant := (3532075370755837996907616579450121452256958395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108297714942321821187/50000000000000000000)
  centralHi := (1732763439077149139/800000000000000000)
  directionLo := (111111111111111111111/50000000000000000000)
  directionHi := (222222222222222222223/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree021.table
  base := (-2961855440347434601931347726999508963177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (170)
      previous := (136)
      next := (0)
      square := (3756062305128534326015277150000000000000)
      linear := (-54694902441615931010243656650000000000000)
      constant := (156634296356313898945338967457004419331407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree021.table
  base := (-6071234849963512400643609196563409506201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-152997376675238720407506987847200000000000000)
      constant := (450912647725736182401409450601767231474097479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/50000000000000000000)
  centralHi := (222222222222222222223/100000000000000000000)
  directionLo := (56927504255331102129/25000000000000000000)
  directionHi := (227710017021324408517/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree022.table
  base := (-3278354969883769147456937986685029805847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-522302620415571653700315127050000000000000)
      constant := (1609529259178851999607701904278512585726393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree022.table
  base := (-6690379696804808703432524528856858814189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-1460638921861581457245227173863900000000000000)
      constant := (4630790366169969148065960615784191782953395979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56927504255331102129/25000000000000000000)
  centralHi := (227710017021324408517/100000000000000000000)
  directionLo := (9322745317068013751/4000000000000000000)
  directionHi := (7283394778959385743/3125000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree023.table
  base := (-444908966399322896276781426328842185891/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-276175559428299964154218672125000000000000)
      constant := (912793471786579318772041144169455131771316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree023.table
  base := (-3619721094790502733517924602672004014631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-772150726823007215411445728551500000000000000)
      constant := (2624474854756727090797288576140266646821583041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9322745317068013751/4000000000000000000)
  centralHi := (7283394778959385743/3125000000000000000)
  directionLo := (238306784328080184551/100000000000000000000)
  directionHi := (29788348041010023069/12500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree024.table
  base := (-951985197082282134419568040695380174947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-32355534294312677939808864525000000000000)
      constant := (114311754455653089058428785667483156850954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree024.table
  base := (-7725041552663317682404850157479128644811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-180884887270049711600061748926900000000000000)
      constant := (656884206710086787007437736238099655967283669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238306784328080184551/100000000000000000000)
  centralHi := (29788348041010023069/12500000000000000000)
  directionLo := (243432247780073828203/100000000000000000000)
  directionHi := (60858061945018457051/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree025.table
  base := (-8054472305982285734719065447941519605457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-1224896231477312955049363557300000000000000)
      constant := (4610740748233280298224512668716736911957983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree025.table
  base := (-8152873134080599640841026944121306799449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-1711626517214880377978220023581200000000000000)
      constant := (6619183267354378228974916052788957410315899839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243432247780073828203/100000000000000000000)
  centralHi := (60858061945018457051/25000000000000000000)
  directionLo := (124225998749988316467/50000000000000000000)
  directionHi := (49690399499995326587/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree026.table
  base := (-4219639481746215811770171297339000109773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-642496614179684752132803995850000000000000)
      constant := (2568662311135999513872213670915540991108387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree026.table
  base := (-4263922761186146439978836990778083958753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-897644524499656675777942153410150000000000000)
      constant := (3685040810964847743327052913845609047897838583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124225998749988316467/50000000000000000000)
  centralHi := (49690399499995326587/20000000000000000000)
  directionLo := (31671539586087166087/12500000000000000000)
  directionHi := (253372316688697328697/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree027.table
  base := (-548412053827657229134588668155285658751/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-37363617367817390374495900725000000000000)
      constant := (158184088506758552772005661846409716284964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree027.table
  base := (-8854193759317222162129696780538194406451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-208772397864860702792616510006600000000000000)
      constant := (907131478285435639669946450407513906718117229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31671539586087166087/12500000000000000000)
  centralHi := (253372316688697328697/100000000000000000000)
  directionLo := (129099444873580562839/50000000000000000000)
  directionHi := (258198889747161125679/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree028.table
  base := (-906412742965158331103826892982035062197/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-702593611061741301349048430250000000000000)
      constant := (3141173826141632116520482065942275799810215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree028.table
  base := (-9135574270068088590065242635083207049733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-1962614112568179298711212873298500000000000000)
      constant := (9001082857943296167522948985432058253462157363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129099444873580562839/50000000000000000000)
  centralHi := (258198889747161125679/100000000000000000000)
  directionLo := (131468439624435912057/50000000000000000000)
  directionHi := (52587375849774364823/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree029.table
  base := (-465554889753399099600248278179507917343/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-366321054751384787978585323725000000000000)
      constant := (1725056398789412971338023101437299293476085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree029.table
  base := (-585946581488890364483008240195291639659/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-1023138322176306136144438578268800000000000000)
      constant := (4940215033478788183623779276983486942958825192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/50000000000000000000)
  centralHi := (52587375849774364823/20000000000000000000)
  directionLo := (267590990639828788447/100000000000000000000)
  directionHi := (8362218457494649639/3125000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree030.table
  base := (-4759144316234826596945250557144917024663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (170)
      previous := (136)
      next := (0)
      square := (3756062305128534326015277150000000000000)
      linear := (-84743400882644205618365873850000000000000)
      constant := (419335303121847644247432902985695746778033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree030.table
  base := (-9575635575103275662344536694982209699811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-236659908459671693985171271086300000000000000)
      constant := (1200213594131883988525587971130124194288628669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267590990639828788447/100000000000000000000)
  centralHi := (8362218457494649639/3125000000000000000)
  directionLo := (272165526975908677577/100000000000000000000)
  directionHi := (136082763487954338789/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree031.table
  base := (-605507021744289761845907845872089971069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-396369553192413062586707540925000000000000)
      constant := (2056395457624966546311513007437442849373644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree031.table
  base := (-9739403105908897015610418373281564598401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-2213601707921478219444205723015800000000000000)
      constant := (11765298219930129701132537104464305583247911511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272165526975908677577/100000000000000000000)
  centralHi := (136082763487954338789/50000000000000000000)
  directionLo := (3458305443885758993/1250000000000000000)
  directionHi := (276664435510860719441/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree032.table
  base := (-306958098590646206050945869455470528517/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-411393802412927199890768649525000000000000)
      constant := (2233173852695675523734680046192855097520984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree032.table
  base := (-2467121454575713817916612736229675106247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-1148632119852955596510935003127450000000000000)
      constant := (6385165851023685559497937720121255114286752834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3458305443885758993/1250000000000000000)
  centralHi := (276664435510860719441/100000000000000000000)
  directionLo := (35136418446315325911/12500000000000000000)
  directionHi := (281091347570522607289/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree033.table
  base := (-9923740279280535051002866651436647099081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-189519134059307260975479892500000000000000)
      constant := (1074358831972127799922328942937070176108271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree033.table
  base := (-4982322558929888255322365633768375785437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-132273709527241342588863016083000000000000000)
      constant := (767601526279773079940029925503252341947630723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/12500000000000000000)
  centralHi := (281091347570522607289/100000000000000000000)
  directionLo := (57089922571845017867/20000000000000000000)
  directionHi := (35681201607403136167/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree034.table
  base := (-9992925294676262564727110349144436769011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-1765769203415821897995563466900000000000000)
      constant := (10435056925935337881083715080119300621710109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree034.table
  base := (-10029403485514795655596288397888001281369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-2464589303274777140177198572733100000000000000)
      constant := (14904616706507346484424321199838197425910272959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57089922571845017867/20000000000000000000)
  centralHi := (35681201607403136167/12500000000000000000)
  directionLo := (36217791140014715081/12500000000000000000)
  directionHi := (289742329120117720649/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree035.table
  base := (-5015787209614163843997156277955188895871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-912933100148939223605903950650000000000000)
      constant := (5615033773835943674739243780485629699434449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree035.table
  base := (-5032038463617975297651239578510182093699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-1274125917529605056877431427986100000000000000)
      constant := (8016776735937937251029073593026146917811811589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36217791140014715081/12500000000000000000)
  centralHi := (289742329120117720649/100000000000000000000)
  directionLo := (146986183948032810583/50000000000000000000)
  directionHi := (293972367896065621167/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree036.table
  base := (-10040866472228558896199172746759514922017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-209551466353326110714228037300000000000000)
      constant := (1339351763177351166442034141279164365701847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree036.table
  base := (-201396059982546263595494202360205364627/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-146217464824646838185140396622850000000000000)
      constant := (955750645926815281580338986345497742560768325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146986183948032810583/50000000000000000000)
  centralHi := (293972367896065621167/100000000000000000000)
  directionLo := (298142396999971959521/100000000000000000000)
  directionHi := (149071198499985979761/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree037.table
  base := (-2004364616868668363427747582532242702357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-1946060194061991545644296770100000000000000)
      constant := (12907269136624180090731613405474441705545415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree037.table
  base := (-10047565019097693536338167474336137214147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29970000000000000000000000000000000000000000
      center := (111690)
      previous := (92106)
      next := (0)
      square := (2501537495215603861126174581900000000000000)
      linear := (-73393970233191244889464633039200000000000000)
      constant := (497686003561842111821060063041339596769201441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298142396999971959521/100000000000000000000)
  centralHi := (149071198499985979761/50000000000000000000)
  directionLo := (151127450097060481611/50000000000000000000)
  directionHi := (302254900194120963223/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree038.table
  base := (-1995065933860927275706410092008127607313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-2006157190944048094860541204500000000000000)
      constant := (13789305633243657373593163527936708319038235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree038.table
  base := (-249955324707796064344007023311679436993/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-1399619715206254517243927852844750000000000000)
      constant := (9833035365706582822667598704131723578225664460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151127450097060481611/50000000000000000000)
  centralHi := (302254900194120963223/100000000000000000000)
  directionLo := (61262438898178763413/20000000000000000000)
  directionHi := (153156097245446908533/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree039.table
  base := (-9902153593533124973993542932537400222117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-229583798647344960452976182100000000000000)
      constant := (1633357022419390785853354289207163398000947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree039.table
  base := (-4961240835957780795623596286429178298039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-160161220122052333781417777162700000000000000)
      constant := (1164360886010302490669242060681168594189861481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61262438898178763413/20000000000000000000)
  centralHi := (153156097245446908533/50000000000000000000)
  directionLo := (19394777838567973847/6250000000000000000)
  directionHi := (310316445417087581553/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree040.table
  base := (-9802959919896050591477543302360733340167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-2126351184708161193293030073300000000000000)
      constant := (15639937972124512505968388064508780599446473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree040.table
  base := (-2455251556512363282409497228031265489173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-1483282246990687490821592136083850000000000000)
      constant := (11145793675137860211180797959890682002342190406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19394777838567973847/6250000000000000000)
  centralHi := (310316445417087581553/100000000000000000000)
  directionLo := (314269680527354455289/100000000000000000000)
  directionHi := (31426968052735445529/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree041.table
  base := (-9678325050489280962087270297836172114509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-2186448181590217742509274507700000000000000)
      constant := (16608433255723878387238401195875270058724771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree041.table
  base := (-2423583926212668130127606091498758491737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-1525113512882903977610424277703400000000000000)
      constant := (11832642026809888699358794140709400839219551614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314269680527354455289/100000000000000000000)
  centralHi := (31426968052735445529/10000000000000000000)
  directionLo := (318173801406141181209/100000000000000000000)
  directionHi := (31817380140614118121/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree042.table
  base := (-1905749709874474428088830593959302074059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-249616130941363810191724326900000000000000)
      constant := (1956184287542643408451765804871831406667345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree042.table
  base := (-2385736183858910525393607877148853014179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-174104975419457829377695157702550000000000000)
      constant := (1393307412627294600250445414664497964024601082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318173801406141181209/100000000000000000000)
  centralHi := (31817380140614118121/10000000000000000000)
  directionLo := (161015297179882650819/50000000000000000000)
  directionHi := (322030594359765301639/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree043.table
  base := (-935466338837110108763309021511807976603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-1153321087677165420470881688250000000000000)
      constant := (9315789448943180719301492198887717769475785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree043.table
  base := (-9367243609556577350734428627826695166503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-3217552089334673902376177121885000000000000000)
      constant := (26534289974448185217603540427880850599681648833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161015297179882650819/50000000000000000000)
  centralHi := (322030594359765301639/100000000000000000000)
  directionLo := (81460434992306556361/25000000000000000000)
  directionHi := (65168347993845245089/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree044.table
  base := (-457822241322426076422793438899395752927/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-591684793059096847539501952725000000000000)
      constant := (4921540947438895830785183232845744720064565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree044.table
  base := (-9167587006767995914577075842467889090389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-3301214621119106875953841405124100000000000000)
      constant := (28029514365029303730691809019267178246655854179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81460434992306556361/25000000000000000000)
  centralHi := (65168347993845245089/20000000000000000000)
  directionLo := (329608821648696131053/100000000000000000000)
  directionHi := (164804410824348065527/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree045.table
  base := (-446720905248459998557533207520667070191/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-67412115808845664982618117925000000000000)
      constant := (576927414415025734514217934161569981841405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree045.table
  base := (-4472140767368090186403750347627985770797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-188048730716863324973972538242400000000000000)
      constant := (1642509588867619551932883408335188087318010163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329608821648696131053/100000000000000000000)
  centralHi := (164804410824348065527/50000000000000000000)
  directionLo := (333333333333333333333/100000000000000000000)
  directionHi := (166666666666666666667/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree046.table
  base := (-69510920934487915429339966848914741959/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-2486933166000500488590496679700000000000000)
      constant := (21881225452119284702667370911654738237665125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree046.table
  base := (-8697592247115341595650135449290543133633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-3468539684687972823109169971602300000000000000)
      constant := (31141235286677068040715500350956620962454570263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333333333333333333333/100000000000000000000)
  centralHi := (166666666666666666667/50000000000000000000)
  directionLo := (1316471431258949749/390625000000000000)
  directionHi := (67403337280458227149/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree047.table
  base := (-105250377327313554701360846238375621481/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-636757540720639259451685278525000000000000)
      constant := (5755414899757387837781001492193831493200780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree047.table
  base := (-8427748277641765552801683837983564804131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-3552202216472405796686834254841400000000000000)
      constant := (32757677017798169033568908241742565482434717541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1316471431258949749/390625000000000000)
  centralHi := (67403337280458227149/20000000000000000000)
  directionLo := (170330107963954351739/50000000000000000000)
  directionHi := (340660215927908703479/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree048.table
  base := (-254003908679970646670947429927972367349/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-72420198882350377417305154125000000000000)
      constant := (671963116853712576155614228245185989550872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree048.table
  base := (-8134947710286943066175680787672629443399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-403984972028537641140499837564500000000000000)
      constant := (3823830647516326696400106116438285532627880921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170330107963954351739/50000000000000000000)
  centralHi := (340660215927908703479/100000000000000000000)
  directionLo := (344265186329548167571/100000000000000000000)
  directionHi := (86066296582387041893/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree049.table
  base := (-1953333334463833239210982881783701230081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-666806039161667534059807495725000000000000)
      constant := (6347062101994868323359557682675520200363439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree049.table
  base := (-1563872357811249050129546824706316479231/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-3719527280041271743842162821319600000000000000)
      constant := (36111612727146870145254199493436931359672768205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344265186329548167571/100000000000000000000)
  centralHi := (86066296582387041893/25000000000000000000)
  directionLo := (86958199124991821527/25000000000000000000)
  directionHi := (347832796499967286109/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree050.table
  base := (-7475814056789352878980674769516241325573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-2727321153528726685455474417300000000000000)
      constant := (26614375316451461417899533283669184452628587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree050.table
  base := (-7481138556972019068128642680870727775317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-3803189811825704717419827104558700000000000000)
      constant := (37849071299955253634269315006170925867722873187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86958199124991821527/25000000000000000000)
  centralHi := (347832796499967286109/100000000000000000000)
  directionLo := (35136418446315325911/10000000000000000000)
  directionHi := (351364184463153259111/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree051.table
  base := (-3557852564766977596180837203093883839889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (170)
      previous := (136)
      next := (0)
      square := (3756062305128534326015277150000000000000)
      linear := (-154856563911710179703984380650000000000000)
      constant := (1548280097925378750091947144172155045440999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree051.table
  base := (-1780101500409611855714975326416869831349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-215936241311674316166527299322100000000000000)
      constant := (2201490964091925027587659248009497993615897942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35136418446315325911/10000000000000000000)
  centralHi := (351364184463153259111/100000000000000000000)
  directionLo := (354860431614918044423/100000000000000000000)
  directionHi := (44357553951864755553/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree052.table
  base := (-6733126081603360155901780667196604572237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-2847515147292839783887963286100000000000000)
      constant := (29152238065028889703732673796357075029648803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree052.table
  base := (-336863738714547758224743188072585331677/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-1985257437697285332287577835518450000000000000)
      constant := (20722449309120107853013321560976490851556691470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354860431614918044423/100000000000000000000)
  centralHi := (44357553951864755553/12500000000000000000)
  directionLo := (22395160411940415701/6250000000000000000)
  directionHi := (358322566591046651217/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree053.table
  base := (-1265636103626100921057930316453754946683/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-2907612144174896333104207720500000000000000)
      constant := (30463955831551910140441627587036229246593385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree053.table
  base := (-6331840540161647890418535976335820682457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-4054177407179003638152819954276000000000000000)
      constant := (43303244485490026305027219057154522180343025727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22395160411940415701/6250000000000000000)
  centralHi := (358322566591046651217/100000000000000000000)
  directionLo := (45218946100276962187/12500000000000000000)
  directionHi := (361751568802215697497/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree054.table
  base := (-23603832985524739495429555784725571589/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (170)
      previous := (136)
      next := (0)
      square := (3756062305128534326015277150000000000000)
      linear := (-164872730058719604573358453050000000000000)
      constant := (1766899321546519406043444984542183731962375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree054.table
  base := (-5904186010151066324101143455957553567119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-459759993218159623525609359723900000000000000)
      constant := (5022429531519448025921633825964546982499526801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45218946100276962187/12500000000000000000)
  centralHi := (361751568802215697497/100000000000000000000)
  directionLo := (11410886614690960697/3125000000000000000)
  directionHi := (73029674334022148461/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree055.table
  base := (-54515371152491570480325566014095402629/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-756951534484752357884174147325000000000000)
      constant := (8293231907031203241438296882321456809676275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree055.table
  base := (-5454382697018541209348430667177687573253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-4221502470747869585308148520754200000000000000)
      constant := (47140754582816864063979224053346458402689548083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11410886614690960697/3125000000000000000)
  centralHi := (73029674334022148461/20000000000000000000)
  directionLo := (368513865595044427679/100000000000000000000)
  directionHi := (2303211659969027673/625000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree056.table
  base := (-38906129761486831990382578205517061707/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-771975783705266495188235255925000000000000)
      constant := (8642542471537673437157975489291299776055456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree056.table
  base := (-2491246216722219558148576607091130539269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-2152582501266151279442906401996650000000000000)
      constant := (24559952013175714314242441611979271625630999859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368513865595044427679/100000000000000000000)
  centralHi := (2303211659969027673/625000000000000000)
  directionLo := (11620278146306604833/3125000000000000000)
  directionHi := (371848900681811354657/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree057.table
  base := (-56079490390777451665122758911655849379/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-87444448102864514721366262725000000000000)
      constant := (999886383978760305693543180295901947111780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree057.table
  base := (-4488568684252975180259103346236460561001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-487647503812970614718164120803600000000000000)
      constant := (5682145353957537059408010290532045569427906679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11620278146306604833/3125000000000000000)
  centralHi := (371848900681811354657/100000000000000000000)
  directionLo := (46894286155928144953/12500000000000000000)
  directionHi := (3001234313979401277/800000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree058.table
  base := (-794142339546826015831186033777472129051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-3208097128585179079185429892500000000000000)
      constant := (37450143331292989157380278591520123787734345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree058.table
  base := (-3972657680706322584259531983576962511577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-4472490066101168506041141370471500000000000000)
      constant := (53198961934077647660448365176541934204053738047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46894286155928144953/12500000000000000000)
  centralHi := (3001234313979401277/800000000000000000)
  directionLo := (378430808131697803691/100000000000000000000)
  directionHi := (94607702032924450923/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree059.table
  base := (-429135747329227860897966557308434767701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-817048531366808907100418581725000000000000)
      constant := (9733216712193495993737345774816033567632438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree059.table
  base := (-1717399700498184661153585133902949520921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-2278076298942800739809402826855300000000000000)
      constant := (27649430419294575369023033360828998330574591231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378430808131697803691/100000000000000000000)
  centralHi := (94607702032924450923/25000000000000000000)
  directionLo := (76335840165856303319/20000000000000000000)
  directionHi := (95419800207320379149/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree060.table
  base := (-2873520195720636135406266512974926648599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-369810124705476908624213195700000000000000)
      constant := (4493786365312871907760856873383225660162609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree060.table
  base := (-2875028417789185105363399264553621591257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-515535014407781605910718881883300000000000000)
      constant := (6382111229491552773698488962794434828374122503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76335840165856303319/20000000000000000000)
  centralHi := (95419800207320379149/25000000000000000000)
  directionLo := (48112522432468813709/12500000000000000000)
  directionHi := (384900179459750509673/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree061.table
  base := (-573011850554240237049697025992248272753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-847097029807837181708540798925000000000000)
      constant := (10495942992776891265250217289394627889907007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree061.table
  base := (-2293374630849501905126530922841583280789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-4723477661454467426774134220188800000000000000)
      constant := (59619379299027108972559712893302644671576588579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48112522432468813709/12500000000000000000)
  centralHi := (384900179459750509673/100000000000000000000)
  directionLo := (388094426590510681029/100000000000000000000)
  directionHi := (38809442659051068103/10000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree062.table
  base := (-168869625832877811580909633286657161697/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-1724242558056702638025203815050000000000000)
      constant := (21775974288586226602199391631718903849512715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree062.table
  base := (-1689863900328148882660350007860176667973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-4807140193238900400351798503427900000000000000)
      constant := (61839992671792287471024801377288992869465142003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388094426590510681029/100000000000000000000)
  centralHi := (38809442659051068103/10000000000000000000)
  directionLo := (195631298462877879397/50000000000000000000)
  directionHi := (78252519385151151759/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree063.table
  base := (-1063491616694211624560827757515831202233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-389842456999495758362961340500000000000000)
      constant := (5016511676994091506349915512982357519179903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree063.table
  base := (-266129648545609262347230549098165685411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-271711262501296298551636821481500000000000000)
      constant := (3561157705742171788774214605459785501180102138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195631298462877879397/50000000000000000000)
  centralHi := (78252519385151151759/20000000000000000000)
  directionLo := (394405318873307736171/100000000000000000000)
  directionHi := (98601329718326934043/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree064.table
  base := (-83291005954181985787159126523510694947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-3568679109877518374482896498900000000000000)
      constant := (46773739772681606594439211344157978168546465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree064.table
  base := (-417358061373028636016340381797340825169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-4974465256807766347507127069906100000000000000)
      constant := (66401915248140624279192351299412474673237834759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394405318873307736171/100000000000000000000)
  centralHi := (98601329718326934043/25000000000000000000)
  directionLo := (198761597999981306347/50000000000000000000)
  directionHi := (79504639199992522539/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree065.table
  base := (252394810428483425796268020909422636097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-3628776106759574923699140933300000000000000)
      constant := (48427351102323778189101850151693663233523857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree065.table
  base := (125800479548995011580132551364123386561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-2529063894296099660542395676572600000000000000)
      constant := (34371610224982840681635196047590028778212362729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198761597999981306347/50000000000000000000)
  centralHi := (79504639199992522539/20000000000000000000)
  directionLo := (80123361676977539847/20000000000000000000)
  directionHi := (100154202096221924809/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree066.table
  base := (943041691231532168309360787776696716099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-409874789293514608101709485300000000000000)
      constant := (5567715307627430111462194427089990270444891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree066.table
  base := (942343984607860422299927070523102661331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-571310035597403588295828404042700000000000000)
      constant := (7902750300318967598023976252801915147890259251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80123361676977539847/20000000000000000000)
  centralHi := (100154202096221924809/25000000000000000000)
  directionLo := (403686713879665555389/100000000000000000000)
  directionHi := (40368671387966555539/10000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree067.table
  base := (1655471549013592305643220840383209586463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-3748970100523688022131629802100000000000000)
      constant := (51819998632497288873183129212471039976503503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree067.table
  base := (827429241636229228150927505153185983007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-2612726426080532634120059959811700000000000000)
      constant := (36773255308603803349069006140259294140469663223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403686713879665555389/100000000000000000000)
  centralHi := (40368671387966555539/10000000000000000000)
  directionLo := (81346689856547229703/20000000000000000000)
  directionHi := (101683362320684037129/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree068.table
  base := (2389672182942036325187832571278356943001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-3809067097405744571347874236500000000000000)
      constant := (53559032705607588970650576993473546912383081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree068.table
  base := (1194566804871814978622208641765607452563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-2654557691972749120908892101431250000000000000)
      constant := (38004246495173282421755204150158646444807258507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81346689856547229703/20000000000000000000)
  centralHi := (101683362320684037129/25000000000000000000)
  directionLo := (102439382858809859/25000000000000000)
  directionHi := (409757531435239436001/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree069.table
  base := (3145633006884906008973448066493284983951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-429907121587533457840457630100000000000000)
      constant := (6147393236722342519989615956198439564855559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree069.table
  base := (1572579988412752181687135246558093549397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-299598773096107289744191582561200000000000000)
      constant := (4361705487852823329311705991036354770622120437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102439382858809859/25000000000000000)
  centralHi := (409757531435239436001/100000000000000000000)
  directionLo := (41275945824459355491/10000000000000000000)
  directionHi := (412759458244593554911/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree070.table
  base := (3923344834394837167686664913488936430181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-3929261091169857669780363105300000000000000)
      constant := (57122517163075533501616643453992603850844661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree070.table
  base := (490366182256585999141940057426226302983/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-2738220223757182094486556384670350000000000000)
      constant := (40526563544542375455242429672921247234045927548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41275945824459355491/10000000000000000000)
  centralHi := (412759458244593554911/100000000000000000000)
  directionLo := (207869854820774521421/50000000000000000000)
  directionHi := (415739709641549042843/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree071.table
  base := (1180699923089434613643352647345748867479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-997339522012978554749151884925000000000000)
      constant := (14736741539377175009173449165935005658265799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree071.table
  base := (2361217508515936822067369120584614527163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-2780051489649398581275388526289900000000000000)
      constant := (41817888566644870174883328940008069820302577907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207869854820774521421/50000000000000000000)
  centralHi := (415739709641549042843/100000000000000000000)
  directionLo := (52337343559491033179/12500000000000000000)
  directionHi := (418698748475928265433/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree072.table
  base := (5543990659483852438331619283653049024847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-449939453881552307579205774900000000000000)
      constant := (6755542839241790214800281767152877441223623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree072.table
  base := (1385917639979432459438233815392364367039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-313542528393512785340468963101050000000000000)
      constant := (4792147124345854071284640134271098642732575038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52337343559491033179/12500000000000000000)
  centralHi := (418698748475928265433/100000000000000000000)
  directionLo := (421637021355783910933/100000000000000000000)
  directionHi := (210818510677891955467/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree073.table
  base := (99795495723883536117407428817757409689/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-1027388020454006829357274102125000000000000)
      constant := (15670318715828188483434909179047813602956944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree073.table
  base := (1277326161577212034177113282859856536617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-5727428042867663109706105619058000000000000000)
      constant := (88921739818528113395611593054139658157444612565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421637021355783910933/100000000000000000000)
  centralHi := (210818510677891955467/50000000000000000000)
  directionLo := (16982198377371377937/4000000000000000000)
  directionHi := (212277479717142224213/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree074.table
  base := (3625778836985964633391439054415530157613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-2084824539349041933322670421450000000000000)
      constant := (32295566832593057441455364560607657942766653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree074.table
  base := (7251311186892618353925624972143669248149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29970000000000000000000000000000000000000000
      center := (111690)
      previous := (92106)
      next := (0)
      square := (2501537495215603861126174581900000000000000)
      linear := (-157056502017624218467128916278300000000000000)
      constant := (2476352739648291034065476714130314576736702553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16982198377371377937/4000000000000000000)
  centralHi := (212277479717142224213/50000000000000000000)
  directionLo := (106863244787063026399/25000000000000000000)
  directionHi := (427452979148252105597/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree075.table
  base := (8137923968869236708334218569530443558987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-469971786175571157317953919700000000000000)
      constant := (7392162399064340983161744957125773992030883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree075.table
  base := (8137707732373675867117971701594548393567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-654972567381836561873492687281800000000000000)
      constant := (10485398049330536731747725654273471430757139007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106863244787063026399/25000000000000000000)
  centralHi := (427452979148252105597/100000000000000000000)
  directionLo := (53791435363991901183/12500000000000000000)
  directionHi := (86066296582387041893/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree076.table
  base := (9046006671715712723205087267856716951361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-4289843072462196965077829711700000000000000)
      constant := (68496258323407930601424559420696394073060241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree076.table
  base := (4522908503431144117506316658288256989419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-2989207819110481015219549234387650000000000000)
      constant := (48576166334157514182797049181669426529299683491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53791435363991901183/12500000000000000000)
  centralHi := (86066296582387041893/20000000000000000000)
  directionLo := (108297714942321821187/25000000000000000000)
  directionHi := (433190859769287284749/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree077.table
  base := (623487647403579311559112592962727023227/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-1087485017336063378573518536525000000000000)
      constant := (17622880895831079746843717310219923555525548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree077.table
  base := (9975636028768953718369315752201855978779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-6062078170005395004016762752014400000000000000)
      constant := (99976301709381883341653723878893136607630824531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108297714942321821187/25000000000000000000)
  centralHi := (433190859769287284749/100000000000000000000)
  directionLo := (4360314860077462993/1000000000000000000)
  directionHi := (436031486007746299301/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree078.table
  base := (10927308051827400218121715037384686001327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-490004118469590007056702064500000000000000)
      constant := (8057250792241071897666269748136462174011943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree078.table
  base := (2731790552703212270226461189725978895781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-341430038988323776533023724180750000000000000)
      constant := (5713360515570800683670017411931327571949835402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4360314860077462993/1000000000000000000)
  centralHi := (436031486007746299301/100000000000000000000)
  directionLo := (10971343143406388343/2500000000000000000)
  directionHi := (438853725736255533721/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree079.table
  base := (11900521162006806595692666645330598015099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-4470134063108366612726563014900000000000000)
      constant := (74567458754168551590298981834671778439223019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree079.table
  base := (11900393306795112920949134467068437722221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-6229403233574260951172091318492600000000000000)
      constant := (105744895131913869716843740151955476990579364469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10971343143406388343/2500000000000000000)
  centralHi := (438853725736255533721/100000000000000000000)
  directionLo := (220828965715019894667/50000000000000000000)
  directionHi := (88331586286007957867/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree080.table
  base := (12895439435189343292349112282037672308181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-4530231059990423161942807449300000000000000)
      constant := (76648128272762734790432458478845051456962661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree080.table
  base := (12895327365583094803717384852717647360431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-6313065765358693924749755601731700000000000000)
      constant := (108689519047941107099941485067609007198150833159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220828965715019894667/50000000000000000000)
  centralHi := (88331586286007957867/20000000000000000000)
  directionLo := (111111111111111111111/25000000000000000000)
  directionHi := (88888888888888888889/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree081.table
  base := (6956030454500063666351056466693366986487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (170)
      previous := (136)
      next := (0)
      square := (3756062305128534326015277150000000000000)
      linear := (-255018225381804428397725104650000000000000)
      constant := (4375403640388879508799464089200240302878383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree081.table
  base := (13911962691327872917400608846466736253781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-710747588571458544258602209441200000000000000)
      constant := (12408262315589459262729305611731941657382835701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/25000000000000000000)
  centralHi := (88888888888888888889/20000000000000000000)
  directionLo := (447213595499957939281/100000000000000000000)
  directionHi := (223606797749978969641/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree082.table
  base := (598015354954088409101813163435896339743/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-4650425053754536260375296318100000000000000)
      constant := (80894870378403297866546953714357690087979575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree082.table
  base := (7475148904534963601345442977831871483323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-3240195414463779935952542084104950000000000000)
      constant := (57349710172724581145426970235190598396914204147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447213595499957939281/100000000000000000000)
  centralHi := (223606797749978969641/50000000000000000000)
  directionLo := (112491426285092149629/25000000000000000000)
  directionHi := (449965705140368598517/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree083.table
  base := (4002601709862514062607621246375003890231/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-1177630512659148202397885188125000000000000)
      constant := (20765235676564799130264987117256375315108711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree083.table
  base := (8005165717501229715738084651598444164753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-3282026680355996422741374225724500000000000000)
      constant := (58882348710506570915047469097917062374985295417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112491426285092149629/25000000000000000000)
  centralHi := (449965705140368598517/100000000000000000000)
  directionLo := (452701084165852502771/100000000000000000000)
  directionHi := (113175271041463125693/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree084.table
  base := (4273032126438412625714544836643064016429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-132517195764406926633549588525000000000000)
      constant := (2368207844590674608754191287929787576147861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree084.table
  base := (534126951586278582710667998056624692353/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-369317549583134767725578485260450000000000000)
      constant := (6715010663499041380425461008253590765351701008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452701084165852502771/100000000000000000000)
  centralHi := (113175271041463125693/25000000000000000000)
  directionLo := (56927504255331102129/12500000000000000000)
  directionHi := (455420034042648817033/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree085.table
  base := (18195547737808564732280330273727038924629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-4830716044400705908024029621300000000000000)
      constant := (87478489383487257360363372770171890152894949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree085.table
  base := (18195489881192887237264507362418512478631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-6731378424280858792638077017927200000000000000)
      constant := (124015903803224296237721224137228851430242912959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56927504255331102129/12500000000000000000)
  centralHi := (455420034042648817033/100000000000000000000)
  directionLo := (229061423645425586101/50000000000000000000)
  directionHi := (458122847290851172203/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree086.table
  base := (19320663543926609883179435837055264735437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-4890813041282762457240274055700000000000000)
      constant := (89729963560601367543200490026801476443570397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree086.table
  base := (9660306437568305725403609039302984581931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-3407520478032645883107870650583150000000000000)
      constant := (63600916453676659478891879133926768657305746659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229061423645425586101/50000000000000000000)
  centralHi := (458122847290851172203/100000000000000000000)
  directionLo := (92161961570345426109/20000000000000000000)
  directionHi := (230404903925863565273/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree087.table
  base := (20467475056770429876712409888084879472167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-550101115351646556272946498900000000000000)
      constant := (10223322762928032291252883128592763915249503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree087.table
  base := (6549577820416068821413930014953929833/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-766522609761080526643711731600600000000000000)
      constant := (14491997685876830676576923575023548029601228125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92161961570345426109/20000000000000000000)
  centralHi := (230404903925863565273/50000000000000000000)
  directionLo := (463481191435871337899/100000000000000000000)
  directionHi := (4634811914358713379/1000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree088.table
  base := (21635981516954951431576670653937324840121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-5011007035046875555672762924500000000000000)
      constant := (94318313239229835658804238038168923312049801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree088.table
  base := (21635942671389217443039408445494048725779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-6982366019634157713371069867644500000000000000)
      constant := (133694342527672818467974156631171189569152907531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463481191435871337899/100000000000000000000)
  centralHi := (4634811914358713379/1000000000000000000)
  directionLo := (466137265853400687551/100000000000000000000)
  directionHi := (7283394778959385743/1562500000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree089.table
  base := (5706545564707555524645939077510056455767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-1267776007982233026222251839725000000000000)
      constant := (24163797156329089126850273565378314572917127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree089.table
  base := (11413074126338777912514611483173287276493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-3533014275709295343474367075441800000000000000)
      constant := (68500461454232774110692695848640215152803032277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466137265853400687551/100000000000000000000)
  centralHi := (7283394778959385743/1562500000000000000)
  directionLo := (234389145663655405553/50000000000000000000)
  directionHi := (468778291327310811107/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree090.table
  base := (6009519174538725584684079588366425409331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-142533361911416351502923660925000000000000)
      constant := (2750570304924675129566881433295297828683979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree090.table
  base := (24038046932258743734320471168484147182091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-794410120355891517836266492680300000000000000)
      constant := (15594191139975565607811571717418893177430543211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234389145663655405553/50000000000000000000)
  centralHi := (468778291327310811107/100000000000000000000)
  directionLo := (471404520791031682933/100000000000000000000)
  directionHi := (235702260395515841467/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree091.table
  base := (25271664321408445431191176271106573578679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-5191298025693045203321496227700000000000000)
      constant := (101414340253550515845435852427959632459872999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree091.table
  base := (1233966712414525466335661061789972377/488281250000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-3616676807493728317052031358680900000000000000)
      constant := (71867367266419113001564224663917243748390686720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471404520791031682933/100000000000000000000)
  centralHi := (235702260395515841467/50000000000000000000)
  directionLo := (474016200171145372241/100000000000000000000)
  directionHi := (237008100085572686121/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree092.table
  base := (2652694467652359683726827039157470559053/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-2625697511287550876268870331050000000000000)
      constant := (51918308208742771216426185958058775576416465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree092.table
  base := (26526921879248912026608819543919786052127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-7317016146771889607681727000600900000000000000)
      constant := (147161965684681461160582191236668321155534310903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474016200171145372241/100000000000000000000)
  centralHi := (237008100085572686121/50000000000000000000)
  directionLo := (238306784328080184551/50000000000000000000)
  directionHi := (476613568656160369103/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree093.table
  base := (27803917364849961859327481951957713917151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-590165779939684255750442788500000000000000)
      constant := (11809706604089189161794271160367619425254359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree093.table
  base := (27803897417383399277338795950658008781853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-822297630950702509028821253760000000000000000)
      constant := (16736601519711085592555279352191882326201210813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238306784328080184551/50000000000000000000)
  centralHi := (476613568656160369103/100000000000000000000)
  directionLo := (23959842947608694083/5000000000000000000)
  directionHi := (479196858952173881661/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree094.table
  base := (582051640683692491234671375054747118311/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-2685794508169607425485114765450000000000000)
      constant := (54383284641486779862268801695685862914579775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree094.table
  base := (14551282291144888285863479806440168546269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-3742170605170377777418527783539550000000000000)
      constant := (77068539238732202162369319921627643849927223141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23959842947608694083/5000000000000000000)
  centralHi := (479196858952173881661/100000000000000000000)
  directionLo := (120441574381548885661/25000000000000000000)
  directionHi := (96353259505239108529/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree095.table
  base := (30422938372727669821971801625971336172749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-5431686013221271400186473965300000000000000)
      constant := (111274245930742321113096167697703678229992669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree095.table
  base := (6084584621181989365889487880130833146961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-7568003742125188528414719850318200000000000000)
      constant := (157684960055150668808665312733526264784166791645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120441574381548885661/25000000000000000000)
  centralHi := (96353259505239108529/20000000000000000000)
  directionLo := (96864420967570523383/20000000000000000000)
  directionHi := (121080526209463154229/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree096.table
  base := (31764986103839412850007657579977104301687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-610198112233703105489190933300000000000000)
      constant := (12645598817522352461536815222219793938715183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree096.table
  base := (15882486374993477159277505600140279929009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-425092570772756750110688007419850000000000000)
      constant := (8959614354668804901145436604655328389005319889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96864420967570523383/20000000000000000000)
  centralHi := (121080526209463154229/25000000000000000000)
  directionLo := (243432247780073828203/50000000000000000000)
  directionHi := (486864495560147656407/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree097.table
  base := (33128724981492565499034031053983029813991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-5551880006985384498618962834100000000000000)
      constant := (116374999543921902506851735747772625414933271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree097.table
  base := (33128713302167543380382884526654370784357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-7735328805694054475570048416796400000000000000)
      constant := (164901373440580222393862376563961401521906563373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243432247780073828203/50000000000000000000)
  centralHi := (486864495560147656407/100000000000000000000)
  directionLo := (244696839394947116693/50000000000000000000)
  directionHi := (489393678789894233387/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree098.table
  base := (34514154786326803266964362241517197110249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-5611977003867441047835207268500000000000000)
      constant := (118968076471636325887488352596762892965930169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree098.table
  base := (3451414457262909704938188372663036045871/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-3909495668739243724573856350017750000000000000)
      constant := (84284952601863315577853041617510557020452946595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244696839394947116693/50000000000000000000)
  centralHi := (489393678789894233387/100000000000000000000)
  directionLo := (98381971649682912551/20000000000000000000)
  directionHi := (122977464562103640689/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree099.table
  base := (35921275322225533178853909029002299075421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-630230444527721955227939078100000000000000)
      constant := (13509957791662110918307851492861020691678789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree099.table
  base := (17960633195579989590649897074307628803273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-439036326070162245706965387959700000000000000)
      constant := (9571036314144617576986055281470806794485126633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98381971649682912551/20000000000000000000)
  centralHi := (122977464562103640689/25000000000000000000)
  directionLo := (24720661623652209829/5000000000000000000)
  directionHi := (494413232473044196581/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree100.table
  base := (37350086413345353911163864833509016825361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-5732170997631554146267696137300000000000000)
      constant := (124239630489646604131492024931514230362854241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree100.table
  base := (1494003144185276999474810478520168104439/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-7986316401047353396303041266513700000000000000)
      constant := (176027618776229437929774155348510573023328406775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24720661623652209829/5000000000000000000)
  centralHi := (494413232473044196581/100000000000000000000)
  directionLo := (124225998749988316467/25000000000000000000)
  directionHi := (496903994999953265869/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree101.table
  base := (19400293950768982485954287556275735964499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-2896133997256805347741970285850000000000000)
      constant := (63459053776444565573900799533058334613124419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree101.table
  base := (38800581074811441405424422013901338341809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-8069978932831786369880705549752800000000000000)
      constant := (179816800553277021975777054292857130507384858201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124225998749988316467/25000000000000000000)
  centralHi := (496903994999953265869/100000000000000000000)
  directionLo := (249691167269380354051/50000000000000000000)
  directionHi := (499382334538760708103/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree102.table
  base := (2517048727757019476773443265317204136397/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-162565694205435201241671805725000000000000)
      constant := (3600695869531350107787489918951419348910292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree102.table
  base := (20136386838232183747886847459720225133611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-452980081367567741303242768499550000000000000)
      constant := (10202566609547709869508346195579912893871221131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249691167269380354051/50000000000000000000)
  centralHi := (499382334538760708103/100000000000000000000)
  directionLo := (501848435139387329993/100000000000000000000)
  directionHi := (250924217569693664997/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree103.table
  base := (20883330755945855680068650958471975774423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-2956230994138861896958214720250000000000000)
      constant := (66180230864950855522490811860236230037728263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree103.table
  base := (41766656295713958924379722278465104755327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-8237303996400652317036034116231000000000000000)
      constant := (187515814019347026653491952006508642001213455703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501848435139387329993/100000000000000000000)
  centralHi := (250924217569693664997/50000000000000000000)
  directionLo := (20172099054062608391/4000000000000000000)
  directionHi := (31518904771972825611/6250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree104.table
  base := (21641116693763369358436705809436759368283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-2986279492579890171566336937450000000000000)
      constant := (67562169411851574590110746893764377508830923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree104.table
  base := (43282228828618231903562942228434669245947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-8320966528185085290613698399470100000000000000)
      constant := (191425645684215746342570216815692492038013816883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20172099054062608391/4000000000000000000)
  centralHi := (31518904771972825611/6250000000000000000)
  directionLo := (506744633377394657393/100000000000000000000)
  directionHi := (253372316688697328697/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree105.table
  base := (44819495164029872339663205242816617243477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-670295109115759654705435367700000000000000)
      constant := (15324075841762992117332967753185349555191293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree105.table
  base := (22409745589968472427512718608560503719377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-466923836664973236899520149039400000000000000)
      constant := (10854205219772435642778286009363386466326444017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506744633377394657393/100000000000000000000)
  centralHi := (253372316688697328697/50000000000000000000)
  directionLo := (509175077217315556287/100000000000000000000)
  directionHi := (7955860581520555567/1562500000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree106.table
  base := (46378446743502437816906109790404302434077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-6092752978923893441565162743700000000000000)
      constant := (140737492978463258044967625281022748497160237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree106.table
  base := (11594610815515652356776918876978763261859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-4244145795876975618884513482974150000000000000)
      constant := (99682979412348302779990786125156596158688565302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509175077217315556287/100000000000000000000)
  centralHi := (7955860581520555567/1562500000000000000)
  directionLo := (102318794961967450853/20000000000000000000)
  directionHi := (255796987404918627133/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree107.table
  base := (23979544018014152971547322100051746768719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-3076424987902974995390703589050000000000000)
      constant := (71793385012104464840744067164304191488266239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree107.table
  base := (2997442812130836978855817013013083075127/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-4285977061769192105673345624593700000000000000)
      constant := (101698220140811457423352949539426424652942063224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102318794961967450853/20000000000000000000)
  centralHi := (255796987404918627133/50000000000000000000)
  directionLo := (20560059566614004569/4000000000000000000)
  directionHi := (257000744582675057113/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree108.table
  base := (24780709479356104192505986818257558729693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (170)
      previous := (136)
      next := (0)
      square := (3756062305128534326015277150000000000000)
      linear := (-345163720704889252222091756250000000000000)
      constant := (8136917428132745957253759627764318028567237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree108.table
  base := (6195177037628595361523298211386944411577/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-480867591962378732495797529579250000000000000)
      constant := (11525952128798113100381780494744094168380160868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20560059566614004569/4000000000000000000)
  centralHi := (257000744582675057113/50000000000000000000)
  directionLo := (516397779494322251357/100000000000000000000)
  directionHi := (258198889747161125679/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree109.table
  base := (51185439434843481546520581681171603718403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-6273043969570063089213896046900000000000000)
      constant := (149370724018791186940919103364574899901190643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree109.table
  base := (12796359278267838037862833098358563136161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-4369639593553625079251009907832800000000000000)
      constant := (105789026463593103885652623190951377915211514258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516397779494322251357/100000000000000000000)
  centralHi := (258198889747161125679/50000000000000000000)
  directionLo := (518783001330166756331/100000000000000000000)
  directionHi := (129695750332541689083/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree110.table
  base := (26415574696584302530173437828383256753751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-3166570483226059819215070240650000000000000)
      constant := (76152700477821336831396631758099043797053831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree110.table
  base := (52831147365020692619828949738366972883383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-8822941718891683132079684098904700000000000000)
      constant := (215729184100853416174840328807194775256065457487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518783001330166756331/100000000000000000000)
  centralHi := (129695750332541689083/25000000000000000000)
  directionLo := (104231461329409545657/20000000000000000000)
  directionHi := (260578653323523864143/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree111.table
  base := (27249274383629058127276169541871852613567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (170)
      previous := (136)
      next := (0)
      square := (3756062305128534326015277150000000000000)
      linear := (-355179886851898677091465828650000000000000)
      constant := (8626030250642394495542396328876846673522103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree111.table
  base := (54498546995746491611463351762707237337627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3330000000000000000000000000000000000000000
      center := (12410)
      previous := (10234)
      next := (0)
      square := (277948610579511540125130509100000000000000)
      linear := (-26746559311339688004977022168600000000000000)
      constant := (660422017515282234209715984512606510033429791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104231461329409545657/20000000000000000000)
  centralHi := (260578653323523864143/50000000000000000000)
  directionLo := (523520843972877620583/100000000000000000000)
  directionHi := (65440105496609702573/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree112.table
  base := (3511727343434712598829318869114454779483/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-1613333740054058184215657337525000000000000)
      constant := (39565038670379445753612854275193083348552492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree112.table
  base := (1755863623366585249398458255549682228487/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-4495133391230274539617506332691450000000000000)
      constant := (112076048058007397687737830236197179402155119088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523520843972877620583/100000000000000000000)
  centralHi := (65440105496609702573/12500000000000000000)
  directionLo := (131468439624435912057/25000000000000000000)
  directionHi := (525873758497743648229/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree113.table
  base := (11579683103579305946841584909972560411819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-6513431957098289286078873784500000000000000)
      constant := (161280231460779241511048684653738886966786695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree113.table
  base := (28949207083334664120396088758240798129651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-4536964657122491026406338474311000000000000000)
      constant := (114211938472554562960436165351124776363798869739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131468439624435912057/25000000000000000000)
  centralHi := (525873758497743648229/100000000000000000000)
  directionLo := (66027024022248404689/12500000000000000000)
  directionHi := (528216192177987237513/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree114.table
  base := (14907720695272933286449349599211808362191/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-182598026499454050980419950525000000000000)
      constant := (4564688190135925145460601457792906275259719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree114.table
  base := (59630881601125423903280363208577609835337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-1017510205114379447376704581317900000000000000)
      constant := (25859541590463132524247277777397284730781187177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66027024022248404689/12500000000000000000)
  centralHi := (528216192177987237513/100000000000000000000)
  directionLo := (8289816934939806909/1562500000000000000)
  directionHi := (530548283836147642177/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree115.table
  base := (15346259808140098579900784343855477410009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-1658406487715600596127840663325000000000000)
      constant := (41851446207412386043459783827352293670210729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree115.table
  base := (2455401528089090967224183330204146601433/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-9241254377813847999968005515100200000000000000)
      constant := (237088088217772657303337812318326315312157598425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8289816934939806909/1562500000000000000)
  centralHi := (530548283836147642177/100000000000000000000)
  directionLo := (106574033851393767591/20000000000000000000)
  directionHi := (133217542314242209489/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree116.table
  base := (31580442411506238324662583476750636031699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-3346861473872229466863803543850000000000000)
      constant := (85255630705527732678855417601616801518567619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree116.table
  base := (63160883923404873233724591114596154994341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-9324916909598280973545669798339300000000000000)
      constant := (241480518650758418298723933768765453031167479149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106574033851393767591/20000000000000000000)
  centralHi := (133217542314242209489/25000000000000000000)
  directionLo := (267590990639828788447/50000000000000000000)
  directionHi := (107036396255931515379/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree117.table
  base := (12991683901114055642877185610041667717171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-750424438291835053660427946900000000000000)
      constant := (19293911620590441659181107764051875047272695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree117.table
  base := (64958418720160069482112706891031044361481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-1045397715709190438569259342397600000000000000)
      constant := (27323685067576791130418970050211418497577807401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267590990639828788447/50000000000000000000)
  centralHi := (107036396255931515379/20000000000000000000)
  directionLo := (67185481235821247103/12500000000000000000)
  directionHi := (21499353995462799073/4000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree118.table
  base := (33388821617762600386744729070717579700407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (1530)
      previous := (1224)
      next := (0)
      square := (33804560746156808934137494350000000000000)
      linear := (-3406958470754286016080047978250000000000000)
      constant := (88403807174401838220525783182328123955732967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree118.table
  base := (8347205318733215412140753332727210445603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-4746120986583573460350499182408750000000000000)
      constant := (125193014542671941021098809697333050556409884268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67185481235821247103/12500000000000000000)
  centralHi := (21499353995462799073/4000000000000000000)
  directionLo := (107955180457698837509/20000000000000000000)
  directionHi := (269887951144247093773/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree119.table
  base := (68618555970124931483947757444562274795933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-6874013938390628581376340390900000000000000)
      constant := (179998490698061632542717896685409544258470573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree119.table
  base := (68618555371590033529564875781300810255753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-9575904504951579894278662648056600000000000000)
      constant := (254899109077677817406370997875273390548450194417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107955180457698837509/20000000000000000000)
  centralHi := (269887951144247093773/50000000000000000000)
  directionLo := (542058263006687465157/100000000000000000000)
  directionHi := (271029131503343732579/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree120.table
  base := (70481157668387046213405699030162583580959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-770456770585853903399176091700000000000000)
      constant := (20357537069974251875878688395271463252228631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree120.table
  base := (14096231429188537122695778314393813297217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-1073285226304001429761814103477300000000000000)
      constant := (28828045064536108186043021791864230868175053285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542058263006687465157/100000000000000000000)
  centralHi := (271029131503343732579/50000000000000000000)
  directionLo := (272165526975908677577/50000000000000000000)
  directionHi := (108866210790363471031/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree121.table
  base := (14473089658187114642217271961825337181187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-6994207932154741679808829259700000000000000)
      constant := (186465643140734125749809532210539261558380735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree121.table
  base := (4522840489683745346123094434251292033807/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-4871614784260222920716995607267400000000000000)
      constant := (132022959295286685173865841693579344678694595384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272165526975908677577/50000000000000000000)
  centralHi := (108866210790363471031/20000000000000000000)
  directionLo := (109318878899989718491/20000000000000000000)
  directionHi := (68324299312493574057/12500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree122.table
  base := (74271427799857515226071914059042439228367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-7054304929036798229025073694100000000000000)
      constant := (189741919227888256366097562761182437577497727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree122.table
  base := (14854285480377210875662150457818895902941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-9826892100304878815011655497773900000000000000)
      constant := (268679648102853858068340520280514997738906122745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109318878899989718491/20000000000000000000)
  centralHi := (68324299312493574057/12500000000000000000)
  directionLo := (274424200782854867323/50000000000000000000)
  directionHi := (548848401565709734647/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree123.table
  base := (76199096158576726310496210475096520382463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-790489102879872753137924236500000000000000)
      constant := (21449629098696443434443903217075868683442167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree123.table
  base := (38099547905634587808882547554502564735141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-550586368449406210477184432278500000000000000)
      constant := (15186310784096031007964955549869688600101672261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274424200782854867323/50000000000000000000)
  centralHi := (548848401565709734647/100000000000000000000)
  directionLo := (110218637934553283737/20000000000000000000)
  directionHi := (275546594836383209343/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree124.table
  base := (1953711333293572117025328752960379039207/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (765)
      previous := (612)
      next := (0)
      square := (16902280373078404467068747175000000000000)
      linear := (-1793624730700227831864390640725000000000000)
      constant := (49094967779752488329262799193497907021757670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree124.table
  base := (78148453028669319338268782472662560362139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-9994217163873744762166984064252100000000000000)
      constant := (278067756619380674528573550295801678655997231571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110218637934553283737/20000000000000000000)
  centralHi := (275546594836383209343/50000000000000000000)
  directionLo := (553328871021721438881/100000000000000000000)
  directionHi := (276664435510860719441/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree125.table
  base := (80119499285133602199976887830849453261681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-7234595919682967876673806997300000000000000)
      constant := (199741546917342130148116452764298805714196161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree125.table
  base := (801194990206773197059547875935644241803/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-5038939847829088867872324173745600000000000000)
      constant := (141411067808052749116900945370814195216464643350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553328871021721438881/100000000000000000000)
  centralHi := (276664435510860719441/50000000000000000000)
  directionLo := (111111111111111111111/20000000000000000000)
  directionHi := (138888888888888888889/25000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree126.table
  base := (82112233985567970403438598388071678228827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (340)
      previous := (272)
      next := (0)
      square := (7512124610257068652030554300000000000000)
      linear := (-810521435173891602876672381300000000000000)
      constant := (22570187697841874201956782453492645104059443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree126.table
  base := (82112233754823040380541894828920275405673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 123210000000000000000000000000000000000000000
      center := (459170)
      previous := (378658)
      next := (0)
      square := (10284098591441926984629828836700000000000000)
      linear := (-1129060247493623412146923625636700000000000000)
      constant := (31957414566700272034490753057080126713273297033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111111111111111111111/20000000000000000000)
  centralHi := (138888888888888888889/25000000000000000000)
  directionLo := (111554670204543406397/20000000000000000000)
  directionHi := (278886675511358515993/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree127.table
  base := (84126657400830067854467874940727230807407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-7354789913447080975106295866100000000000000)
      constant := (206550298206104676689143601770598905695399967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree127.table
  base := (84126657199511731164032104909263164092467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1108890000000000000000000000000000000000000000
      center := (4132530)
      previous := (3407922)
      next := (0)
      square := (92556887322977342861668459530300000000000000)
      linear := (-10245204759227043682899976913969400000000000000)
      constant := (292451543068468014503712410471088008003049573163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111554670204543406397/20000000000000000000)
  centralHi := (278886675511358515993/50000000000000000000)
  directionLo := (559982363037962336603/100000000000000000000)
  directionHi := (139995590759490584151/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree128.table
  base := (86162769499601148537685587667487862975897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (3060)
      previous := (2448)
      next := (0)
      square := (67609121492313617868274988700000000000000)
      linear := (-7414886910329137524322540300500000000000000)
      constant := (209997373691388738335468422316266516901047657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree128.table
  base := (43081384661983731187176639182488562784103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 554445000000000000000000000000000000000000000
      center := (2066265)
      previous := (1703961)
      next := (0)
      square := (46278443661488671430834229765150000000000000)
      linear := (-5164433645505738328238820598604250000000000000)
      constant := (148663285758594742373586746070041374238566397567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell026.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559982363037962336603/100000000000000000000)
  centralHi := (139995590759490584151/25000000000000000000)
  directionLo := (562182695141045214577/100000000000000000000)
  directionHi := (281091347570522607289/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree129.table
  base := (22055142562849850005268507240714710293743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (85)
      previous := (68)
      next := (0)
      square := (1878031152564267163007638575000000000000)
      linear := (-207638441866977613153855131525000000000000)
      constant := (5929803214832222943044224150066432392643687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 301
  qDenominator := 666
  table := BinomialMassData.Q301_666.Degree129.table
  base := (1102757126227284056769059815951537379251/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 61605000000000000000000000000000000000000000
      center := (229585)
      previous := (189329)
      next := (0)
      square := (5142049295720963492314914418350000000000000)
      linear := (-578473879044217201669739193358200000000000000)
      constant := (16791212024618853129065741136084068181990062840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q301_666.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell026.Kernel129
