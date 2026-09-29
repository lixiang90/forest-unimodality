import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell025.Parameters
import ForestUnimodality.BinomialMassData.Q67_153.Batch000_049
import ForestUnimodality.BinomialMassData.Q67_153.Batch050_099
import ForestUnimodality.BinomialMassData.Q67_153.Batch100_149
import ForestUnimodality.BinomialMassData.Q4_9.Batch000_049
import ForestUnimodality.BinomialMassData.Q4_9.Batch050_099
import ForestUnimodality.BinomialMassData.Q4_9.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree000.table
  base := (2632535271239500364703012299/100000000000000000000000000)
  polynomial :=
    { denominator := 25500000000000000000000000000000000000000
      center := (86)
      previous := (67)
      next := (0)
      square := (1747350702044229049658685688500000000000)
      linear := (6956410131884131431423412425000000000000)
      constant := (671296494166072592999268136245000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree000.table
  base := (2632535271239500364703012299/100000000000000000000000000)
  polynomial :=
    { denominator := 1500000000000000000000000000000000000000
      center := (5)
      previous := (4)
      next := (0)
      square := (102785335414366414685805040500000000000)
      linear := (409200595993184201848436025000000000000)
      constant := (39488029068592505470545184485000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree001.table
  base := (163349825726328190111478228514805433807509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (16603715122086908327070364375320000000000000)
      constant := (1266322441389536555400700752955536799999992727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree001.table
  base := (80934066335446327371005440441062847622709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (28605226806237264991494839010000000000000)
      constant := (2170679062069134429426512651628696885813143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24806483286729862061/50000000000000000000)
  directionHi := (49612966573459724123/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree002.table
  base := (3268674539837379973120987993657836729463/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (2980203810152093618496271682535000000000000)
      constant := (200408285510168663461994376695356799999998312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree002.table
  base := (51435848410260056053642582885038267333077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (20382399973087951816630435770000000000000)
      constant := (1363341038804810611233687658776033217993079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24806483286729862061/50000000000000000000)
  centralHi := (49612966573459724123/100000000000000000000)
  directionLo := (70163330197749763299/100000000000000000000)
  directionHi := (701633301977497633/1000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree003.table
  base := (17361058586684250556657273283319596622699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (201053204420273350580550252360000000000000)
      constant := (14531573869192123242515452008515590271880033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree003.table
  base := (6791231867490740339231186990651223254241/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3000000000000000000000000000000000000000
      center := (10)
      previous := (8)
      next := (0)
      square := (205570670828732829371610081000000000000)
      linear := (270212736443080858705911834000000000000)
      constant := (19647952983519254842758371715953669762723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70163330197749763299/100000000000000000000)
  centralHi := (701633301977497633/1000000000000000000)
  directionLo := (5370761176215539381/6250000000000000000)
  directionHi := (85932178819448630097/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree004.table
  base := (23942097833459176646492478445003908665481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (1277507738825653383907265719890000000000000)
      constant := (176379736830811875767914132039445499316748243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree004.table
  base := (46648548095029760849472510876515821545997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (7873492613578650933803258580000000000000)
      constant := (1187040043105935269809960688705927181741919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5370761176215539381/6250000000000000000)
  centralHi := (85932178819448630097/100000000000000000000)
  directionLo := (24806483286729862061/25000000000000000000)
  directionHi := (19845186629383889649/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree005.table
  base := (6842393819267225320453497011748699354987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (52632)
      previous := (41004)
      next := (0)
      square := (1069378629651068178391115641362000000000000)
      linear := (-425576880765445417054149241080000000000000)
      constant := (49196313513629543452108807053225101066963561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree005.table
  base := (33249775315854133000937028745664153669531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-8572161052719975415925547900000000000000)
      constant := (825428437721335834451085402132932149077337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24806483286729862061/25000000000000000000)
  centralHi := (19845186629383889649/20000000000000000000)
  directionLo := (11093796582368075671/10000000000000000000)
  directionHi := (110937965823680756711/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree006.table
  base := (12589842704741660716662043971960547526697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (14620)
      previous := (11390)
      next := (0)
      square := (297049619347518938441976567045000000000000)
      linear := (-378376904739208941019779102810000000000000)
      constant := (9858878746880955959863884915209794705646299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree006.table
  base := (24433485263626806671055928382951608847797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-2779757191002066862850483820000000000000)
      constant := (66094782819064930447676802908854826543391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11093796582368075671/10000000000000000000)
  centralHi := (110937965823680756711/100000000000000000000)
  directionLo := (60763226365367136247/50000000000000000000)
  directionHi := (24305290546146854499/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree007.table
  base := (3785029211047354324682098949437039662863/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (52632)
      previous := (41004)
      next := (0)
      square := (1069378629651068178391115641362000000000000)
      linear := (-2298736833356858958288260299152000000000000)
      constant := (26532697598867631203790479732455220489319989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree007.table
  base := (733517289287443249295468132228037390889/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (180)
      previous := (144)
      next := (0)
      square := (3700272074917190928688981458000000000000)
      linear := (-8292693677063445623076632172000000000000)
      constant := (89009346398062994320606097162785047770015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60763226365367136247/50000000000000000000)
  centralHi := (24305290546146854499/20000000000000000000)
  directionLo := (131263571357534773709/100000000000000000000)
  directionHi := (13126357135753477371/10000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree008.table
  base := (14374482696856913178106365936269932285987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-16176584048262828644526579140940000000000000)
      constant := (103213184588011745636289536461354281627556561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree008.table
  base := (1737573062819594694189401777241889065987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-14477280512903963616277991835000000000000)
      constant := (86830285291299312656180355011062009563298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131263571357534773709/100000000000000000000)
  centralHi := (13126357135753477371/10000000000000000000)
  directionLo := (70163330197749763299/50000000000000000000)
  directionHi := (140326660395499526599/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree009.table
  base := (2725753953660900562887817732154464907549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-579430109159482291600329355170000000000000)
      constant := (2339848137018270936119788945425421074844983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree009.table
  base := (1313657587238612638634829303623785438629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-2065410436608735578190021495000000000000)
      constant := (7920760436717304969704658561742712631774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70163330197749763299/50000000000000000000)
  centralHi := (140326660395499526599/100000000000000000000)
  directionLo := (74419449860189586183/50000000000000000000)
  directionHi := (148838899720379172367/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree010.table
  base := (8142726483034078865254811210986820178539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-25542383811219896350697134431300000000000000)
      constant := (72855881352109964098860415785330157853139817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree010.table
  base := (3903162343392148137917560128316448102049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-45400214692106553582284790150000000000000)
      constant := (124434630055410167314719785464544098755323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74419449860189586183/50000000000000000000)
  centralHi := (148838899720379172367/100000000000000000000)
  directionLo := (156889975849932232671/100000000000000000000)
  directionHi := (4902811745310382271/3125000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree011.table
  base := (1468220389792524950850394549010429042821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-7556320923174607550945603019120000000000000)
      constant := (16838712283161376254731486126105877821132263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree011.table
  base := (2789349073526053055881972341490047141047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-53623041525255866757149193390000000000000)
      constant := (116366839817328360175188689340231272808269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156889975849932232671/100000000000000000000)
  centralHi := (4902811745310382271/3125000000000000000)
  directionLo := (41136898715152579481/25000000000000000000)
  directionHi := (6581903794424412717/4000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree012.table
  base := (1978908476315858832744391115129038577897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (14620)
      previous := (11390)
      next := (0)
      square := (297049619347518938441976567045000000000000)
      linear := (-1939343531898720225381538317870000000000000)
      constant := (3704047187595418160799206695896876447036699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree012.table
  base := (1847994368469045653203966108925512042793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (50)
      previous := (40)
      next := (0)
      square := (1027853354143664146858050405000000000000)
      linear := (-6871763150933908881334844070000000000000)
      constant := (12956668948079315260546521846776536128379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41136898715152579481/25000000000000000000)
  centralHi := (6581903794424412717/4000000000000000000)
  directionLo := (5370761176215539381/3125000000000000000)
  directionHi := (171864357638897260193/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree013.table
  base := (2311473181646008670948251347287338307591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-39591083455655497909952967366840000000000000)
      constant := (70138359948051905465466297997073100814132573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree013.table
  base := (64862650224759763380987452635978963739/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-35034347595777246553438999935000000000000)
      constant := (62024592468346208248820384109371456167624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5370761176215539381/3125000000000000000)
  centralHi := (171864357638897260193/100000000000000000000)
  directionLo := (4472052372712249369/2500000000000000000)
  directionHi := (178882094908489974761/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree014.table
  base := (877116200413413737566026023015613630407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-44273983337134031763038245012020000000000000)
      constant := (77308685087274681213652150750550833158065821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree014.table
  base := (331508087409945665719277725969553324191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-78291522024703806281742403110000000000000)
      constant := (137948175558833242666723665721177939753157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4472052372712249369/2500000000000000000)
  centralHi := (178882094908489974761/100000000000000000000)
  directionLo := (46408680714838554107/25000000000000000000)
  directionHi := (185634722859354216429/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree015.table
  base := (-76862782815351621911477485300650851281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5848)
      previous := (4556)
      next := (0)
      square := (118819847739007575376790626818000000000000)
      linear := (-1087930738191390347024967170160000000000000)
      constant := (1952867560336298499151167323794335711939373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree015.table
  base := (-289737587707494563915890031991713682303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (50)
      previous := (40)
      next := (0)
      square := (1027853354143664146858050405000000000000)
      linear := (-9612705428650346606289645150000000000000)
      constant := (17533118799272531600936612904024858953091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46408680714838554107/25000000000000000000)
  centralHi := (185634722859354216429/100000000000000000000)
  directionLo := (96075096647477382059/50000000000000000000)
  directionHi := (192150193294954764119/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree016.table
  base := (-375236197358685463088753790483195958717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-13409945775022774867302200075595000000000000)
      constant := (25407486363346373911473507831499621934131249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree016.table
  base := (-1679174857443000996062994875507906494117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-189474351382004865262942419180000000000000)
      constant := (366460480104973938191539795001286524658841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96075096647477382059/50000000000000000000)
  centralHi := (192150193294954764119/100000000000000000000)
  directionLo := (24806483286729862061/12500000000000000000)
  directionHi := (198451866293838896489/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree017.table
  base := (-19951308168238130718692496334345945573/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 918000000000000000000000000000000000000000
      center := (3096)
      previous := (2412)
      next := (0)
      square := (62904625273592245787712684786000000000000)
      linear := (-686149211547878039085812681736000000000000)
      constant := (1392899624080762094789457988297380274549825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree017.table
  base := (-265673312289864959662368359563910400527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27000000000000000000000000000000000000000
      center := (90)
      previous := (72)
      next := (0)
      square := (1850136037458595464344490729000000000000)
      linear := (-20592000504830349161267122566000000000000)
      constant := (42793181947773994972653756507774419185771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24806483286729862061/12500000000000000000)
  centralHi := (198451866293838896489/100000000000000000000)
  directionLo := (204559501582612736451/100000000000000000000)
  directionHi := (51139875395653184113/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree018.table
  base := (-3379705876181960226903933618213953516227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-7000620318116463019486595065860000000000000)
      constant := (15338885505908035089025850398368502301431191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree018.table
  base := (-3528350624087203388952376546959723534709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-24707295412733568662488892460000000000000)
      constant := (55508082099217928335223558199120829395873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204559501582612736451/100000000000000000000)
  centralHi := (51139875395653184113/25000000000000000000)
  directionLo := (105244995296624644949/50000000000000000000)
  directionHi := (210489990593249289899/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree019.table
  base := (-2085786747962929494472771872360083483853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-33844241372263350514232316618960000000000000)
      constant := (80243523708657814281912205883529268575495041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree019.table
  base := (-538388917167380159382641229165279517459/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-59702828095225186078032209655000000000000)
      constant := (145257492747429480927159414085074906057214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105244995296624644949/50000000000000000000)
  centralHi := (210489990593249289899/100000000000000000000)
  directionLo := (216257907582972342203/100000000000000000000)
  directionHi := (54064476895743085551/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree020.table
  base := (-4880416509936697186769983159144398771543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-72371382626005234881549910883100000000000000)
      constant := (185622647927438861066889770023196256385649971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree020.table
  base := (-500381345472602999649776960656091288843/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27000000000000000000000000000000000000000
      center := (90)
      previous := (72)
      next := (0)
      square := (1850136037458595464344490729000000000000)
      linear := (-25525696604719937066185764510000000000000)
      constant := (67201196458206925377962315662285535201239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216257907582972342203/100000000000000000000)
  centralHi := (54064476895743085551/25000000000000000000)
  directionLo := (221875931647361513421/100000000000000000000)
  directionHi := (110937965823680756711/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree021.table
  base := (-1378838166999570374414917121691589514669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-2140396736318993575962088570230000000000000)
      constant := (5927378480054971383544278650740891890781977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree021.table
  base := (-351719230883289635606766735866970541743/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-7547294992041611028099623655000000000000)
      constant := (21452065285753744460720202309596353499084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221875931647361513421/100000000000000000000)
  centralHi := (110937965823680756711/50000000000000000000)
  directionLo := (113677587387096527773/50000000000000000000)
  directionHi := (227355174774193055547/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree022.table
  base := (-3042049830317272332363964059094338526487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-40868591194481151293860233086730000000000000)
      constant := (121857879170888853795711947272806876477821939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree022.table
  base := (-3092930936349455343663890756442410894277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-144074136689898311680657629030000000000000)
      constant := (440805048521066514013200396056054905854521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113677587387096527773/50000000000000000000)
  centralHi := (227355174774193055547/100000000000000000000)
  directionLo := (11635272015387425207/5000000000000000000)
  directionHi := (232705440307748504141/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree023.table
  base := (-1318648723877834380387688846985566547117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (52632)
      previous := (41004)
      next := (0)
      square := (1069378629651068178391115641362000000000000)
      linear := (-17284016454088167288161148763728000000000000)
      constant := (55312331104479939738764149463529624232846049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree023.table
  base := (-6685419639258698408869157860108131201539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-304593927046095249711044064540000000000000)
      constant := (999842526328550286894196813537080457558447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11635272015387425207/5000000000000000000)
  centralHi := (232705440307748504141/100000000000000000000)
  directionLo := (5948385726451459607/2500000000000000000)
  directionHi := (237935429058058384281/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree024.table
  base := (-1762109053316232036497448462757778127427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-2530638393108871397052528373995000000000000)
      constant := (8663311579183788008714599813949006363520791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree024.table
  base := (-891474068466364786861761571796992689151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-8917766130899829890577024195000000000000)
      constant := (31300559060849325312615265609218043865094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5948385726451459607/2500000000000000000)
  centralHi := (237935429058058384281/100000000000000000000)
  directionLo := (60763226365367136247/25000000000000000000)
  directionHi := (243052905461468544989/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree025.table
  base := (-1863636323931432869889979950317281046627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-23946470508349476036744074777250000000000000)
      constant := (87407614616462190913000611139861755993169519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree025.table
  base := (-7529808416311086389412604813359414985559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-337485234378692502410501677500000000000000)
      constant := (1262412545536930367917988520039295795389907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60763226365367136247/25000000000000000000)
  centralHi := (243052905461468544989/100000000000000000000)
  directionLo := (248064832867298620611/100000000000000000000)
  directionHi := (62016208216824655153/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree026.table
  base := (-3907887020471185004501353438246858589409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-50234390957438219000030788377090000000000000)
      constant := (194891291500021112557385969033239762426841573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree026.table
  base := (-246363427759232344470815621212557973339/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-88482722011247782190057620995000000000000)
      constant := (351626849599653995989598936178087477758776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248064832867298620611/100000000000000000000)
  centralHi := (62016208216824655153/25000000000000000000)
  directionLo := (31622185585662211897/12500000000000000000)
  directionHi := (252977484685297695177/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree027.table
  base := (-6356060724103218029954302042332395647/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 433500000000000000000000000000000000000000
      center := (1462)
      previous := (1139)
      next := (0)
      square := (29704961934751893844197656704500000000000)
      linear := (-584176009979749843628593635552000000000000)
      constant := (2401706802108067739958999232090560030339264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree027.table
  base := (-128075784754563014274811960205439624247/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-10288237269758048753054424735000000000000)
      constant := (43305768070533741777682493570138898036144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31622185585662211897/12500000000000000000)
  centralHi := (252977484685297695177/100000000000000000000)
  directionLo := (16112283528646618143/6250000000000000000)
  directionHi := (257796536458345890289/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree028.table
  base := (-8417643954596155749344428998429186123703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-109834581677833505706232132044540000000000000)
      constant := (477179821872374063272569653483097060676745491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree028.table
  base := (-4236287946750419101446662353734920983347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-193411097688794190729844048470000000000000)
      constant := (859914721745163829100401132929157133449631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16112283528646618143/6250000000000000000)
  centralHi := (257796536458345890289/100000000000000000000)
  directionLo := (262527142715069547419/100000000000000000000)
  directionHi := (13126357135753477371/5000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree029.table
  base := (-866416010529891891490886517316455414817/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (26316)
      previous := (20502)
      next := (0)
      square := (534689314825534089195557820681000000000000)
      linear := (-11451748155931203955931740968972000000000000)
      constant := (52437909372389383867334297009070698398182949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree029.table
  base := (-8713492528949495225341677030738291089789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-403267849043887007809416903420000000000000)
      constant := (1888900259760208449543386753210066140575697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262527142715069547419/100000000000000000000)
  centralHi := (13126357135753477371/5000000000000000000)
  directionLo := (267174001568935830581/100000000000000000000)
  directionHi := (133587000784467915291/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree030.table
  base := (-8877670638763835584867560410848785123049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-13244486826754508156933631926100000000000000)
      constant := (63765176672685042048579433359794103298316517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree030.table
  base := (-8921923725951397711792739255077717689619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-46634833634465070462127301100000000000000)
      constant := (229573040252821716365678986234766846931143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267174001568935830581/100000000000000000000)
  centralHi := (133587000784467915291/50000000000000000000)
  directionLo := (271741409370336779337/100000000000000000000)
  directionHi := (135870704685168389669/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree031.table
  base := (-9060226100417671843943533302501600874693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-123883281322269107265487964980080000000000000)
      constant := (625686310457223626805091729859690008374770521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree031.table
  base := (-9099880289414018069979590225852208778133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-436159156376484260508874516380000000000000)
      constant := (2251546459303386896435181505741990362990409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271741409370336779337/100000000000000000000)
  centralHi := (135870704685168389669/50000000000000000000)
  directionLo := (276233307221986156887/100000000000000000000)
  directionHi := (34529163402748269611/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree032.table
  base := (-9213605232253833821166094504290060935573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-128566181203747641118573242625260000000000000)
      constant := (679764375409294035752157747905264654519723881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree032.table
  base := (-9249102701655842778286908276992692271963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-452604810042782886858603322860000000000000)
      constant := (2445020557821583662059212327081197308656999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276233307221986156887/100000000000000000000)
  centralHi := (34529163402748269611/12500000000000000000)
  directionLo := (280653320790999053197/100000000000000000000)
  directionHi := (140326660395499526599/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree033.table
  base := (-4669675635804309641954975189502917548043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (14620)
      previous := (11390)
      next := (0)
      square := (297049619347518938441976567045000000000000)
      linear := (-7402726726957009720647695570580000000000000)
      constant := (40894930168302304099977117812555970485846719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree033.table
  base := (-9371097690375208773666129612074544535001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-52116718189897945912036903260000000000000)
      constant := (294059886242458960762834951403776366394997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280653320790999053197/100000000000000000000)
  centralHi := (140326660395499526599/50000000000000000000)
  directionLo := (142502397280918272047/50000000000000000000)
  directionHi := (57000958912367308819/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree034.table
  base := (-9438803305665046648220724206144840282489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (15480)
      previous := (12060)
      next := (0)
      square := (314523126367961228938563423930000000000000)
      linear := (-8113645939217924048514341053860000000000000)
      constant := (46747586142375108720410520563059518310337549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree034.table
  base := (-946716977057791501931015316226220897677/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27000000000000000000000000000000000000000
      center := (90)
      previous := (72)
      next := (0)
      square := (1850136037458595464344490729000000000000)
      linear := (-48549611737538013955806093582000000000000)
      constant := (285606649247987127884787994125892035762721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142502397280918272047/50000000000000000000)
  centralHi := (57000958912367308819/20000000000000000000)
  directionLo := (289290821450411532509/100000000000000000000)
  directionHi := (28929082145041153251/10000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree035.table
  base := (-951312339328416171407145622175749706627/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (26316)
      previous := (20502)
      next := (0)
      square := (534689314825534089195557820681000000000000)
      linear := (-14261488084818324267782907556080000000000000)
      constant := (85555597203680741871714030178137625039189519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree035.table
  base := (-9538448482464599115245123939638089261737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-501941771041678765907789742300000000000000)
      constant := (3073572609129388342805602547629771589933101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289290821450411532509/100000000000000000000)
  centralHi := (28929082145041153251/10000000000000000000)
  directionLo := (146757134262421052817/50000000000000000000)
  directionHi := (58702853704968421127/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree036.table
  base := (-9563320047821092315140406568247445382899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-16366420081073530725657150356220000000000000)
      constant := (102071321827669235858209001484769464853026567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree036.table
  base := (-4792955965355567327099161439409839499229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (50)
      previous := (40)
      next := (0)
      square := (1027853354143664146858050405000000000000)
      linear := (-28799301372665410680973252710000000000000)
      constant := (183279495405801847318613655361770481502313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146757134262421052817/50000000000000000000)
  centralHi := (58702853704968421127/20000000000000000000)
  directionLo := (297677799440758344733/100000000000000000000)
  directionHi := (148838899720379172367/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree037.table
  base := (-9590268582315162524372106878605591934313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-151980680611140310383999630851160000000000000)
      constant := (983959907589378114526014803984430566136555661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree037.table
  base := (-480520356902013022193004502880451079037/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13500000000000000000000000000000000000000
      center := (45)
      previous := (36)
      next := (0)
      square := (925068018729297732172245364500000000000)
      linear := (-26741653918713800930362367763000000000000)
      constant := (176620927369574602891428525290227820866001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297677799440758344733/100000000000000000000)
  centralHi := (148838899720379172367/50000000000000000000)
  directionLo := (37722986761247358227/12500000000000000000)
  directionHi := (301783894089978865817/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree038.table
  base := (-2398682186033978068405264811705218554733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-39165895123154711059271227124085000000000000)
      constant := (262876019287286968508820248451624179617418401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree038.table
  base := (-2403166912654210409889365323087213207391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-137819683010143661239244040435000000000000)
      constant := (943428923411028350473086677116645243400443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37722986761247358227/12500000000000000000)
  centralHi := (301783894089978865817/100000000000000000000)
  directionLo := (152917432937133440599/50000000000000000000)
  directionHi := (305834865874266881199/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree039.table
  base := (-9577360004989256242966198703536170608953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-17927386708233042010018909571280000000000000)
      constant := (124585473252290127667002628087224140082037749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree039.table
  base := (-9593328770251359616505735678139790734133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-63080487300763696811856107580000000000000)
      constant := (446989466990379365199506814325580627797601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152917432937133440599/50000000000000000000)
  centralHi := (305834865874266881199/100000000000000000000)
  directionLo := (154916438472931306973/50000000000000000000)
  directionHi := (309832876945862613947/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree040.table
  base := (-9538734821005416835716799615511229738493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-166029380255575911943255463786700000000000000)
      constant := (1193250987078583814016220513036165874350539121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree040.table
  base := (-477647036789588285971326156292984564259/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13500000000000000000000000000000000000000
      center := (45)
      previous := (36)
      next := (0)
      square := (925068018729297732172245364500000000000)
      linear := (-29208501968658594882821688735000000000000)
      constant := (213998610937525001311536544980089416765007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154916438472931306973/50000000000000000000)
  centralHi := (309832876945862613947/100000000000000000000)
  directionLo := (313779951699864465343/100000000000000000000)
  directionHi := (4902811745310382271/1562500000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree041.table
  base := (-4739675067161203738225707445038651589287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-85356140068527222898170370715940000000000000)
      constant := (633722691466781475161442563112018401648793539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree041.table
  base := (-949198013143508133624580665505444912573/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27000000000000000000000000000000000000000
      center := (90)
      previous := (72)
      next := (0)
      square := (1850136037458595464344490729000000000000)
      linear := (-60061569303947052400616258118000000000000)
      constant := (454490387338205104272385387895352987360529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313779951699864465343/100000000000000000000)
  centralHi := (4902811745310382271/1562500000000000000)
  directionLo := (79419497189366426971/25000000000000000000)
  directionHi := (63535597751493141577/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree042.table
  base := (-4699818675323409253754564667007633910437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (14620)
      previous := (11390)
      next := (0)
      square := (297049619347518938441976567045000000000000)
      linear := (-9744176667696276647190334393170000000000000)
      constant := (74658282254267779637874756311184381399651121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree042.table
  base := (-2352714940389520074991532182209002304009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-17140592964049143065441427435000000000000)
      constant := (133824695030274845632885045013372993087973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79419497189366426971/25000000000000000000)
  centralHi := (63535597751493141577/20000000000000000000)
  directionLo := (80382192910342299197/25000000000000000000)
  directionHi := (321528771641369196789/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree043.table
  base := (-2324992748902715198478137789969302914423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-45019519975002878375627824180560000000000000)
      constant := (355614789396211730528257640821367029358757331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree043.table
  base := (-9309937198964022651461538775596220422133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-633507000372067776705620194140000000000000)
      constant := (5098318007408342205307154789618902048602409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80382192910342299197/25000000000000000000)
  centralHi := (321528771641369196789/100000000000000000000)
  directionLo := (325333978313712219191/100000000000000000000)
  directionHi := (40666747289214027399/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree044.table
  base := (-4590338112750751104896677672846245441201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-92380489890745023677798287183710000000000000)
      constant := (751636538381568202947445257711460746822308597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree044.table
  base := (-9189522185318375083874978998487174901099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-649952654038366403055349000620000000000000)
      constant := (5386782469312426729578873946880846277670327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (325333978313712219191/100000000000000000000)
  centralHi := (40666747289214027399/12500000000000000000)
  directionLo := (329095189721220635849/100000000000000000000)
  directionHi := (6581903794424412717/2000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree045.table
  base := (-9042035344440252192385956755148612613693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-21049319962552064578742428001400000000000000)
      constant := (176254292810292038520953925648036152863928169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree045.table
  base := (-4524941519157320853049846646274097269293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (50)
      previous := (40)
      next := (0)
      square := (1027853354143664146858050405000000000000)
      linear := (-37022128205814723855837655950000000000000)
      constant := (315726397901356855814383417061177708192121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329095189721220635849/100000000000000000000)
  centralHi := (6581903794424412717/2000000000000000000)
  directionLo := (83203474367760567533/25000000000000000000)
  directionHi := (332813897471042270133/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree046.table
  base := (-1110536682474051551160938164866774539777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-48531694886111778765441782414445000000000000)
      constant := (417875980150137823895463612151129116532240138) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree046.table
  base := (-355650087968277120897646122627686783027/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (180)
      previous := (144)
      next := (0)
      square := (3700272074917190928688981458000000000000)
      linear := (-136568792274192731150961322716000000000000)
      constant := (1197437962046094276386197948453262284291355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83203474367760567533/25000000000000000000)
  centralHi := (332813897471042270133/100000000000000000000)
  directionLo := (336491510742967582953/100000000000000000000)
  directionHi := (168245755371483791477/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree047.table
  base := (-8707663390027705548801381954467828900271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-198809679425925648914852407302960000000000000)
      constant := (1758917272064386006437866587440877531091185387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree047.table
  base := (-8713831036296350082750776786016634002201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-699289615037262282104535420060000000000000)
      constant := (6299120976386440528049150353737550881940573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336491510742967582953/100000000000000000000)
  centralHi := (168245755371483791477/50000000000000000000)
  directionLo := (170064681264441192179/50000000000000000000)
  directionHi := (340129362528882384359/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree048.table
  base := (-8512329924057840336262423057386561784737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-22610286589711575863104187216460000000000000)
      constant := (205391916419583824008092668771805850932633021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree048.table
  base := (-4258897002182361642784684070881296063571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (50)
      previous := (40)
      next := (0)
      square := (1027853354143664146858050405000000000000)
      linear := (-39763070483531161580792457030000000000000)
      constant := (367714663911845657069598980107356111809287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170064681264441192179/50000000000000000000)
  centralHi := (340129362528882384359/100000000000000000000)
  directionLo := (5370761176215539381/1562500000000000000)
  directionHi := (68745743055558904077/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree049.table
  base := (-2074613379479076576501571106848076206243/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-52043869797220679155255740648330000000000000)
      constant := (485083148924431801412583905228891961362685871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree049.table
  base := (-1660658449314263974650392322170269552937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (180)
      previous := (144)
      next := (0)
      square := (3700272074917190928688981458000000000000)
      linear := (-146436184473971906960798606604000000000000)
      constant := (1389282930289102985799659535189402722070701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5370761176215539381/1562500000000000000)
  centralHi := (68745743055558904077/20000000000000000000)
  directionLo := (69458153202843613771/20000000000000000000)
  directionHi := (43411345751777258607/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree050.table
  base := (-8066173503244315686997793732054698847607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-212858379070361250474108240238500000000000000)
      constant := (2034332228624007996147758843058777184892122579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree050.table
  base := (-8070456713676164805711749305174681408323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-748626576036158161153721839500000000000000)
      constant := (7281769543812799159368042268760283601975279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69458153202843613771/20000000000000000000)
  centralHi := (43411345751777258607/12500000000000000000)
  directionLo := (21926040686796801031/6250000000000000000)
  directionHi := (350816650988748816497/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree051.table
  base := (-488475679510402513279453713282767854049/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 127500000000000000000000000000000000000000
      center := (430)
      previous := (335)
      next := (0)
      square := (8736753510221145248293428442500000000000)
      linear := (-355459606130457163933322741640000000000000)
      constant := (3481250330806452212958621530407815357774004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree051.table
  base := (-1954850216344203623403106319626282931117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-21252006380623799652873629055000000000000)
      constant := (211803487891756680424280435581121151206649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21926040686796801031/6250000000000000000)
  centralHi := (350816650988748816497/100000000000000000000)
  directionLo := (88576862478012855741/25000000000000000000)
  directionHi := (70861489982410284593/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree052.table
  base := (-7546870694575369626761525743051812782209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-222224178833318318180278795528860000000000000)
      constant := (2228910697325976822124043431696006704860423173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree052.table
  base := (-1887555752457540606613041288665006747221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-195379470842188853463294863115000000000000)
      constant := (1993970014499150703125001792646044817825033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88576862478012855741/25000000000000000000)
  centralHi := (70861489982410284593/20000000000000000000)
  directionLo := (4472052372712249369/1250000000000000000)
  directionHi := (357764189816979949521/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree053.table
  base := (-7260044216420736979055968561337527857791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-226907078714796852033364073174040000000000000)
      constant := (2329488001249147212845050914656473270125656827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree053.table
  base := (-7263008329891582409425318093856007839857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-797963537035054040202908258940000000000000)
      constant := (8334630725555791018305529310425887788323861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4472052372712249369/1250000000000000000)
  centralHi := (357764189816979949521/100000000000000000000)
  directionLo := (90296962146996981533/25000000000000000000)
  directionHi := (361187848587987926133/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree054.table
  base := (-1391042136231913882415528405370900187759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5848)
      previous := (4556)
      next := (0)
      square := (118819847739007575376790626818000000000000)
      linear := (-5146443968806119686365541129316000000000000)
      constant := (54050144353030327637756240752991429537212947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree054.table
  base := (-3478915319040565058024202242771793339729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (50)
      previous := (40)
      next := (0)
      square := (1027853354143664146858050405000000000000)
      linear := (-45244955038964037030702059190000000000000)
      constant := (483398642991264644972539780551684619980813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90296962146996981533/25000000000000000000)
  centralHi := (361187848587987926133/100000000000000000000)
  directionLo := (364579358192202817483/100000000000000000000)
  directionHi := (91144839548050704371/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree055.table
  base := (-3316219455471872948316607134505126605309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-118136439238876959869767314232200000000000000)
      constant := (1268607822109189151538389378983331497098773873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree055.table
  base := (-1326950779328577964864007430363930299/2000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13500000000000000000000000000000000000000
      center := (45)
      previous := (36)
      next := (0)
      square := (925068018729297732172245364500000000000)
      linear := (-41542742218382564645118293595000000000000)
      constant := (453775643793846515529730242145043470481750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364579358192202817483/100000000000000000000)
  centralHi := (91144839548050704371/25000000000000000000)
  directionLo := (367939607642419703067/100000000000000000000)
  directionHi := (91984901910604925767/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree056.table
  base := (-6291788679278771401349885743291217823793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-240955778359232453592619906109580000000000000)
      constant := (2644364979832524435708096641748458627320943221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree056.table
  base := (-6293833534179974390438234089000300308059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-847300498033949919252094678380000000000000)
      constant := (9457641135086007074454849203436991891682407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367939607642419703067/100000000000000000000)
  centralHi := (91984901910604925767/25000000000000000000)
  directionLo := (46408680714838554107/12500000000000000000)
  directionHi := (371269445718708432857/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree057.table
  base := (-5933311902689442615304236188117293610007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-27293186471190109716189464861640000000000000)
      constant := (305967121958240017003124437059012306440123931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree057.table
  base := (-593511758612144533540730090713735162961/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3000000000000000000000000000000000000000
      center := (10)
      previous := (8)
      next := (0)
      square := (205570670828732829371610081000000000000)
      linear := (-9597179463336094951131372054000000000000)
      constant := (109417322827926769333548143111858794511117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46408680714838554107/12500000000000000000)
  centralHi := (371269445718708432857/100000000000000000000)
  directionLo := (187284841736121438971/50000000000000000000)
  directionHi := (374569683472242877943/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree058.table
  base := (-5557053675286059546007028260605443763867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-250321578122189521298790461399940000000000000)
      constant := (2865232645723942784078242152301135722310545799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree058.table
  base := (-1111729536523950847017479590641281656957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (180)
      previous := (144)
      next := (0)
      square := (3700272074917190928688981458000000000000)
      linear := (-176038361073309434390310458268000000000000)
      constant := (2049053102029004122947966308684685395262161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187284841736121438971/50000000000000000000)
  centralHi := (374569683472242877943/100000000000000000000)
  directionLo := (377841096532279626669/100000000000000000000)
  directionHi := (37784109653227962667/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree059.table
  base := (-5163053166965653269960532823374273547929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-255004478003668055151875739045120000000000000)
      constant := (2978950318489165795368516078517520543505510013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree059.table
  base := (-2582229952155748000829907451273561525501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-448318729516422899150640548910000000000000)
      constant := (5325379763901826567993725186135613838811473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377841096532279626669/100000000000000000000)
  centralHi := (37784109653227962667/10000000000000000000)
  directionLo := (381084427234877551407/100000000000000000000)
  directionHi := (23817776702179846963/6250000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree060.table
  base := (-4751344403242076810760810804761125270143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-28854153098349621000551224076700000000000000)
      constant := (343872983379860510195091294306272104390786019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree060.table
  base := (-1188146380908496100394159571674703657807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-25363419797198456240305830675000000000000)
      constant := (307334451753708314779666195284975889026579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (381084427234877551407/100000000000000000000)
  centralHi := (23817776702179846963/6250000000000000000)
  directionLo := (96075096647477382059/25000000000000000000)
  directionHi := (384300386589909528237/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree061.table
  base := (-172878277692845399181111566482762794117/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (52632)
      previous := (41004)
      next := (0)
      square := (1069378629651068178391115641362000000000000)
      linear := (-52874055553325024571609258867096000000000000)
      constant := (642590402173999855659798014594017009587525245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree061.table
  base := (-2161525823509031757642633409399601724763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-464764383182721525500369355390000000000000)
      constant := (5742553492130463206404674876066210753431399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96075096647477382059/25000000000000000000)
  centralHi := (384300386589909528237/100000000000000000000)
  directionLo := (3874896561011314881/1000000000000000000)
  directionHi := (387489656101131488101/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree062.table
  base := (-1937458231487008863813159698207025233897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-134526588824051828355565785990330000000000000)
      constant := (1666617799735739129903760707447610582099901709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree062.table
  base := (-775176354244812973495840315640261241347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (180)
      previous := (144)
      next := (0)
      square := (3700272074917190928688981458000000000000)
      linear := (-189194884006348335470093503452000000000000)
      constant := (2382791811354681085408965201749712946483631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3874896561011314881/1000000000000000000)
  centralHi := (387489656101131488101/100000000000000000000)
  directionLo := (78130577890501329377/20000000000000000000)
  directionHi := (195326444726253323443/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree063.table
  base := (-3410245274972379425205499734721446339199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-30415119725509132284912983291760000000000000)
      constant := (383967493571114813025682473451906506023914467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree063.table
  base := (-3411096265310019297674085733787668186051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-106935563744226700411132924860000000000000)
      constant := (1372288436745152171345276603838636995441847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78130577890501329377/20000000000000000000)
  centralHi := (195326444726253323443/50000000000000000000)
  directionLo := (49223839259075540141/12500000000000000000)
  directionHi := (393790714072604321129/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree064.table
  base := (-1463981381147632189884400842304392587123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-139209488705530362208651063635510000000000000)
      constant := (1790183693811237983919201511655978824642679231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree064.table
  base := (-2928712788182037750523352932790702270501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-978865727364338930049925130220000000000000)
      constant := (12795017129269353762491697321054651038696473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49223839259075540141/12500000000000000000)
  centralHi := (393790714072604321129/100000000000000000000)
  directionLo := (396903732587677792977/100000000000000000000)
  directionHi := (198451866293838896489/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree065.table
  base := (-2428085767970325419218932436624387400083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-283101877292539258270387404916200000000000000)
      constant := (3707215304492661436613178877421769905117152351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree065.table
  base := (-2428746650344094848550799423020769635743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-995311381030637556399653936700000000000000)
      constant := (13247222239078750773389307169578439219834939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396903732587677792977/100000000000000000000)
  centralHi := (198451866293838896489/50000000000000000000)
  directionLo := (399992524172952605893/100000000000000000000)
  directionHi := (199996262086476302947/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree066.table
  base := (-955314464121100008698827500454541029039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (14620)
      previous := (11390)
      next := (0)
      square := (297049619347518938441976567045000000000000)
      linear := (-15988043176334321784637371253410000000000000)
      constant := (213125059919109600963726808146025912927823187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree066.table
  base := (-1911211127310520244625798591776822671083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-112417448299659575861042527020000000000000)
      constant := (1523023433521741519352538433184669531986751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399992524172952605893/100000000000000000000)
  centralHi := (199996262086476302947/50000000000000000000)
  directionLo := (403057645810706966021/100000000000000000000)
  directionHi := (201528822905353483011/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree067.table
  base := (-1375604962745896547237311032485775514409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-292467677055496325976557960206560000000000000)
      constant := (3967474610525098139706122968997903493661066573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree067.table
  base := (-1376117731145304407254468660625568313671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1028202688363234809099111549660000000000000)
      constant := (14174982806294394722192648316323109655530883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403057645810706966021/100000000000000000000)
  centralHi := (201528822905353483011/50000000000000000000)
  directionLo := (406099633462883759097/100000000000000000000)
  directionHi := (203049816731441879549/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree068.table
  base := (-823024926482135498780297359251763376599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (15480)
      previous := (12060)
      next := (0)
      square := (314523126367961228938563423930000000000000)
      linear := (-17479445702174991754684896344220000000000000)
      constant := (241228577304345104806264666004823440610141059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree068.table
  base := (-164695289145414551838025686062838006609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (180)
      previous := (144)
      next := (0)
      square := (3700272074917190928688981458000000000000)
      linear := (-208929668405906687089768071228000000000000)
      constant := (2930107536662038206206874962988303373821557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406099633462883759097/100000000000000000000)
  centralHi := (203049816731441879549/50000000000000000000)
  directionLo := (204559501582612736451/50000000000000000000)
  directionHi := (409119003165225472903/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree069.table
  base := (-63224607156759310259027302363843206499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-8384263244957038713409125430470000000000000)
      constant := (117680128180829929891911958739298047939965367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree069.table
  base := (-202636744471430956311028647078157749/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3000000000000000000000000000000000000000
      center := (10)
      previous := (8)
      next := (0)
      square := (205570670828732829371610081000000000000)
      linear := (-11789933285509245131095212918000000000000)
      constant := (168154169988173989878157924233345690844125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204559501582612736451/50000000000000000000)
  centralHi := (409119003165225472903/100000000000000000000)
  directionLo := (206058126024628668631/50000000000000000000)
  directionHi := (412116252049257337263/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree070.table
  base := (83691544363761414606615497657281961043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-76629094174982981883953448285525000000000000)
      constant := (1093567736587957044957094316774219771142018529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree070.table
  base := (535066083941845912339587922860930911/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54000000000000000000000000000000000000000
      center := (180)
      previous := (144)
      next := (0)
      square := (3700272074917190928688981458000000000000)
      linear := (-215507929872426137629659593820000000000000)
      constant := (3124999090070416051158171172439655641824625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206058126024628668631/50000000000000000000)
  centralHi := (412116252049257337263/100000000000000000000)
  directionLo := (103772964824462540009/25000000000000000000)
  directionHi := (415091859297850160037/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree071.table
  base := (29373800912585648450498736390117715313/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-77799819145352615347224767696820000000000000)
      constant := (1128561188257488125911024660770394208260698712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree071.table
  base := (117456717040720518026613550223554671151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-273496325757107328624506693895000000000000)
      constant := (4030974490399398198514375390972071952242154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103772964824462540009/25000000000000000000)
  centralHi := (415091859297850160037/100000000000000000000)
  directionLo := (418046287039563917083/100000000000000000000)
  directionHi := (104511571759890979271/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree072.table
  base := (78134080578003304804622751577595537281/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 433500000000000000000000000000000000000000
      center := (1462)
      previous := (1139)
      next := (0)
      square := (29704961934751893844197656704500000000000)
      linear := (-1754900980349383306899913046847000000000000)
      constant := (25868922140377047891595703781305775330822627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree072.table
  base := (1562410715992251052133875202822408547717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-123381217410525326760861731340000000000000)
      constant := (1847842519998563036738689799048467225643151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418046287039563917083/100000000000000000000)
  centralHi := (104511571759890979271/25000000000000000000)
  directionLo := (105244995296624644949/25000000000000000000)
  directionHi := (420979981186498579797/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree073.table
  base := (550730158132795541316201716689605340227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-80141269086091882273767406519410000000000000)
      constant := (1200188650052883248625919975609276490469791281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree073.table
  base := (2202682333665357439811842035075047235917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1126876610361026567197484388540000000000000)
      constant := (17145049473009964427125566622707026275369759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105244995296624644949/25000000000000000000)
  centralHi := (420979981186498579797/100000000000000000000)
  directionLo := (105973343054988340931/25000000000000000000)
  directionHi := (16955734888798134549/4000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree074.table
  base := (572134783021072464134201521409410449467/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (52632)
      previous := (41004)
      next := (0)
      square := (1069378629651068178391115641362000000000000)
      linear := (-65049595245169212589630980744564000000000000)
      constant := (989458112117186185148580572850709629737191001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree074.table
  base := (357558041149741880846425252990090544487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-285830566006831298386803298755000000000000)
      constant := (4416824556410577770114185218021464889402298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105973343054988340931/25000000000000000000)
  centralHi := (16955734888798134549/4000000000000000000)
  directionLo := (13337089872744182407/3125000000000000000)
  directionHi := (17071475037112553481/4000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree075.table
  base := (141437492135884002764760074209885633217/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5848)
      previous := (4556)
      next := (0)
      square := (118819847739007575376790626818000000000000)
      linear := (-7331797246829435484472004030400000000000000)
      constant := (113244751865837506823078176840449854219995695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree075.table
  base := (1767876501912851090666422242168968004039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (50)
      previous := (40)
      next := (0)
      square := (1027853354143664146858050405000000000000)
      linear := (-64431550982979101105385666750000000000000)
      constant := (1010962713223192871387021041726506904012117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13337089872744182407/3125000000000000000)
  centralHi := (17071475037112553481/4000000000000000000)
  directionLo := (5370761176215539381/1250000000000000000)
  directionHi := (429660894097243150481/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree076.table
  base := (4228707181130182658046911541373864370253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-334613775988803130654325459013180000000000000)
      constant := (5246924392124000350282284848557100263681084159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree076.table
  base := (528568143176632500307204994497498853179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-294053392839980611561667701995000000000000)
      constant := (4683785305851946267986609991062864938071666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5370761176215539381/1250000000000000000)
  centralHi := (429660894097243150481/100000000000000000000)
  directionLo := (432515815165944684407/100000000000000000000)
  directionHi := (54064476895743085551/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree077.table
  base := (4938980400841036947191720745462667999251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-339296675870281664507410736658360000000000000)
      constant := (5400022210510210294260731223240635198398155553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree077.table
  base := (4938837963674620903458242659608968179707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1192659225026221072596399614460000000000000)
      constant := (19280735306475545776016360775569442140852089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432515815165944684407/100000000000000000000)
  centralHi := (54064476895743085551/12500000000000000000)
  directionLo := (435352014834984837227/100000000000000000000)
  directionHi := (108838003708746209307/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree078.table
  base := (5666754222390636362782933608769319068017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-38219952861306688706721779367060000000000000)
      constant := (617256363082223646068747322520562999631970739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree078.table
  base := (283331451702007016774180108790613067139/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1500000000000000000000000000000000000000
      center := (5)
      previous := (4)
      next := (0)
      square := (102785335414366414685805040500000000000)
      linear := (-6717249326069553883034046783000000000000)
      constant := (110189505676429762190873126798371839201417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435352014834984837227/100000000000000000000)
  centralHi := (108838003708746209307/25000000000000000000)
  directionLo := (54771232080739145097/12500000000000000000)
  directionHi := (438169856645913160777/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree079.table
  base := (1603006564890008858557655008214120338459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-87165618908309683053395322987180000000000000)
      constant := (1428194886298435369962313915583072281000995577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree079.table
  base := (3205958124504295065796867302189365977557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-612775266179409162647928613710000000000000)
      constant := (10197634156175345783230733271679112881394039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54771232080739145097/12500000000000000000)
  centralHi := (438169856645913160777/100000000000000000000)
  directionLo := (110242423131172409847/25000000000000000000)
  directionHi := (440969692524689639389/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree080.table
  base := (3587397216832946230398144154950971281557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-176672687757358633033333284796950000000000000)
      constant := (2936219513325715087330729025693082428909989271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree080.table
  base := (1793674443997836908239972811117652753057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-310499046506279237911396508475000000000000)
      constant := (5241051782193914020135223929900176624332539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110242423131172409847/25000000000000000000)
  centralHi := (440969692524689639389/100000000000000000000)
  directionLo := (221875931647361513421/50000000000000000000)
  directionHi := (443751863294723026843/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree081.table
  base := (1591011386654476218843150536158244911709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1734000000000000000000000000000000000000000
      center := (5848)
      previous := (4556)
      next := (0)
      square := (118819847739007575376790626818000000000000)
      linear := (-7956183897693239998216707716424000000000000)
      constant := (134095237732854336579107280630407198338451703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree081.table
  base := (1988743005194521944585952084158548894081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-34956717769205988277647634455000000000000)
      constant := (598359095221904776665056034192475646682243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221875931647361513421/50000000000000000000)
  centralHi := (443751863294723026843/100000000000000000000)
  directionLo := (4465166991611375171/1000000000000000000)
  directionHi := (446516699161137517101/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree082.table
  base := (1094101522399685158376193788624152441317/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-90677793819418583443209281221065000000000000)
      constant := (1549579886713107272864455536191328522999193102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree082.table
  base := (8752737595874714782005021696838559475999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1274887493357714204345043646860000000000000)
      constant := (22125429172527098618449838544374641105851973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4465166991611375171/1000000000000000000)
  centralHi := (446516699161137517101/100000000000000000000)
  directionLo := (224632260084107808779/50000000000000000000)
  directionHi := (449264520168215617559/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree083.table
  base := (1913611758823442397093670127172421156341/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (52632)
      previous := (41004)
      next := (0)
      square := (1069378629651068178391115641362000000000000)
      linear := (-73478815031830573525184480505888000000000000)
      constant := (1272908112505224597432305538845604402282928823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree083.table
  base := (1195999161632868286794949950327261568131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-322833286756003207673693113335000000000000)
      constant := (5679428082442335608156398375857672124679074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224632260084107808779/50000000000000000000)
  centralHi := (449264520168215617559/100000000000000000000)
  directionLo := (451995636631811136453/100000000000000000000)
  directionHi := (225997818315905568227/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree084.table
  base := (10400795576163034869285694028732901742273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-41341886115625711275445297797180000000000000)
      constant := (725883192846816292021045885804751425810550691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree084.table
  base := (5200369029809018024780961571914825339557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (50)
      previous := (40)
      next := (0)
      square := (1027853354143664146858050405000000000000)
      linear := (-72654377816128414280250069990000000000000)
      constant := (1295432048405096402960636133195744476018671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451995636631811136453/100000000000000000000)
  centralHi := (225997818315905568227/50000000000000000000)
  directionLo := (454710349548386111093/100000000000000000000)
  directionHi := (227355174774193055547/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree085.table
  base := (703188842249203190291516114256247201071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1147500000000000000000000000000000000000000
      center := (3870)
      previous := (3015)
      next := (0)
      square := (78630781591990307234640855982500000000000)
      linear := (-5540586395913381401942543497350000000000000)
      constant := (98581530263971175297488786324961969861166356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree085.table
  base := (225019419553927675447970605178771935001/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27000000000000000000000000000000000000000
      center := (90)
      previous := (72)
      next := (0)
      square := (1850136037458595464344490729000000000000)
      linear := (-132422445435661008339423006630000000000000)
      constant := (2392562277231249987301664575099134211225135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454710349548386111093/100000000000000000000)
  centralHi := (227355174774193055547/50000000000000000000)
  directionLo := (114352237745549472791/25000000000000000000)
  directionHi := (91481790196439578233/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree086.table
  base := (378710486776260196169597640523126995417/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-95360693700897117296294558866245000000000000)
      constant := (1719081630589701561912929675062255679561910808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree086.table
  base := (12118691246469986319158441457033171872917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1340670108022908709743958872780000000000000)
      constant := (24541250011209280206920983117579895640568759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114352237745549472791/25000000000000000000)
  centralHi := (91481790196439578233/20000000000000000000)
  directionLo := (460091724432046207461/100000000000000000000)
  directionHi := (230045862216023103731/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree087.table
  base := (13003937077264091329838853224264890496451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-42902852742785222559807057012240000000000000)
      constant := (783477346954874168432756335339347660060423017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree087.table
  base := (1300389816664117657809332708831984587191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3000000000000000000000000000000000000000
      center := (10)
      previous := (8)
      next := (0)
      square := (205570670828732829371610081000000000000)
      linear := (-15079064018768970401040974214000000000000)
      constant := (279607317434455991588747306630495953761573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460091724432046207461/100000000000000000000)
  centralHi := (230045862216023103731/50000000000000000000)
  directionLo := (462758945178883794403/100000000000000000000)
  directionHi := (115689736294720948601/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree088.table
  base := (13906625276056875505189152395305979060639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-390808574566545536891348790755340000000000000)
      constant := (7228452853183747088512072018038012554610166117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree088.table
  base := (13906591127020041467825140112395219623311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1373561415355505962443416485740000000000000)
      constant := (25795848429485649328018261918394670929829397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462758945178883794403/100000000000000000000)
  centralHi := (115689736294720948601/25000000000000000000)
  directionLo := (465410880615497008281/100000000000000000000)
  directionHi := (232705440307748504141/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree089.table
  base := (7413399779605941069703752914001389818819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-197745737224012035372217034200260000000000000)
      constant := (3703898354668674965566885731216807844756244657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree089.table
  base := (1853346199111164559668769421924637164701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-347501767255451147198286323055000000000000)
      constant := (6608704894481436080054223875843930406893854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465410880615497008281/100000000000000000000)
  centralHi := (232705440307748504141/50000000000000000000)
  directionLo := (46804779055937401233/10000000000000000000)
  directionHi := (468047790559374012331/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree090.table
  base := (985278711785588067908894285262316451473/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-11115954842486183461042204056825000000000000)
      constant := (210814657968205996886529027159789713453708364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree090.table
  base := (15764433095918295619998826281706634562233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-156272524743122579460319344300000000000000)
      constant := (3009063555752932795327008954845119903686699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46804779055937401233/10000000000000000000)
  centralHi := (468047790559374012331/100000000000000000000)
  directionLo := (235334963774898349007/50000000000000000000)
  directionHi := (94133985509959339603/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree091.table
  base := (3343920858391527913300739445455608125829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (52632)
      previous := (41004)
      next := (0)
      square := (1069378629651068178391115641362000000000000)
      linear := (-80971454842196227690120924738176000000000000)
      constant := (1554609156410717654504170272013352110205843687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree091.table
  base := (2089947653177391192199619627607712603497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-355724594088600460373150726295000000000000)
      constant := (6934026422487257477131528475550816480588838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235334963774898349007/50000000000000000000)
  centralHi := (94133985509959339603/20000000000000000000)
  directionLo := (473277537130117875891/100000000000000000000)
  directionHi := (118319384282529468973/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree092.table
  base := (4423058463656590056993557099387695489371/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-102385043523114918075922475334015000000000000)
      constant := (1989737747923892792542715149593182187903561913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree092.table
  base := (17692213620766466638636814463241416185791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1439344030020700467842331711660000000000000)
      constant := (28398420632706764078995286634667518237016357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473277537130117875891/100000000000000000000)
  centralHi := (118319384282529468973/25000000000000000000)
  directionLo := (5948385726451459607/1250000000000000000)
  directionHi := (475870858116116768561/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree093.table
  base := (18682347711803695288005119816151878575643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-46024785997104245128530575442360000000000000)
      constant := (905227034770561070458969260522713678725082481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree093.table
  base := (4670582491206322681832119319466867737143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-40438602324638863727557236615000000000000)
      constant := (807458800596859784224007525418400603211429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5948385726451459607/1250000000000000000)
  centralHi := (475870858116116768561/100000000000000000000)
  directionLo := (239225061425631453687/50000000000000000000)
  directionHi := (3827600982810103259/800000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree094.table
  base := (3937989108445658315655630349289136667423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (52632)
      previous := (41004)
      next := (0)
      square := (1069378629651068178391115641362000000000000)
      linear := (-83781194771083348001972091325284000000000000)
      constant := (1667464548653044265125610506091375133415901669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree094.table
  base := (4922482494563128938439263317054031709037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-368058834338324430135447331155000000000000)
      constant := (7436598562186832761096341163520458856143999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239225061425631453687/50000000000000000000)
  centralHi := (3827600982810103259/800000000000000000)
  directionLo := (481015557449660665773/100000000000000000000)
  directionHi := (240507778724830332887/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree095.table
  base := (207150270625287950443361227025024738207/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3901500000000000000000000000000000000000000
      center := (13158)
      previous := (10251)
      next := (0)
      square := (267344657412767044597778910340500000000000)
      linear := (-21179443686844763693147286713580000000000000)
      constant := (426489464023746978448795930621768840161146105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree095.table
  base := (5178753353638960115709503055346920479027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 67500000000000000000000000000000000000000
      center := (225)
      previous := (180)
      next := (0)
      square := (4625340093646488660861226822500000000000)
      linear := (-372170247754899086722879532775000000000000)
      constant := (7608013226958152095517821383994366852933729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481015557449660665773/100000000000000000000)
  centralHi := (240507778724830332887/50000000000000000000)
  directionLo := (96713476405478679771/20000000000000000000)
  directionHi := (60445922753424174857/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree096.table
  base := (21757592022339311769446562818718783986673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-47585752624263756412892334657420000000000000)
      constant := (969382546956733254882450903142069185716445491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree096.table
  base := (5439395013952228054661337998951860112181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-41809073463497082590034637155000000000000)
      constant := (864597022023854797887556430636855580336543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96713476405478679771/20000000000000000000)
  centralHi := (60445922753424174857/12500000000000000000)
  directionLo := (486105810922937089977/100000000000000000000)
  directionHi := (243052905461468544989/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree097.table
  base := (22817640200054182006267896567603611223673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-432954673499852341569116289561960000000000000)
      constant := (8921283667943011537517964764145600978378320419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree097.table
  base := (22817629708935320136555033475653748913241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1521572298352193599590975744060000000000000)
      constant := (31826713898612760976142753498802651220657507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486105810922937089977/100000000000000000000)
  centralHi := (243052905461468544989/50000000000000000000)
  directionLo := (488631052907268160429/100000000000000000000)
  directionHi := (48863105290726816043/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree098.table
  base := (5973792849784526452806696423496725226889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-109409393345332718855550391801785000000000000)
      constant := (2280077878734652838560983940407804946945414867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree098.table
  base := (23895162202485610106324509830935301450673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1538017952018492225940704550540000000000000)
      constant := (32535716220465437877666902759195253139168171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488631052907268160429/100000000000000000000)
  centralHi := (48863105290726816043/10000000000000000000)
  directionLo := (98228662276849668619/20000000000000000000)
  directionHi := (61392913923031042887/12500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree099.table
  base := (24990185444918697073461350343102003690719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-49146719251423267697254093872480000000000000)
      constant := (1035725162470492235032990652469859437199853373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree099.table
  base := (24990177383841628524356979179315985129703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-172718178409421205810048150780000000000000)
      constant := (3694722194921790364580818403697947955389109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98228662276849668619/20000000000000000000)
  centralHi := (61392913923031042887/12500000000000000000)
  directionLo := (246821392290915476887/50000000000000000000)
  directionHi := (19745711383273238151/4000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree100.table
  base := (26102682181798129032656489041094151790907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-447003373144287943128372122497500000000000000)
      constant := (9524928508616337978466166359137657666424447321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree100.table
  base := (13051337558395632834316415746214004059537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-785454629675544739320081081750000000000000)
      constant := (16988532248213530112164806325147778109607499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246821392290915476887/50000000000000000000)
  centralHi := (19745711383273238151/4000000000000000000)
  directionLo := (248064832867298620611/50000000000000000000)
  directionHi := (496129665734597241223/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree101.table
  base := (544653229416577196797396135856311185111/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (26316)
      previous := (20502)
      next := (0)
      square := (534689314825534089195557820681000000000000)
      linear := (-45168627302576647698145740014268000000000000)
      constant := (973051765300012727470438971421084980887105665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree101.table
  base := (27232655279424263937646549638221207171661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1587354913017388104989890969980000000000000)
      constant := (34709410443566701751732994847671972593634847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248064832867298620611/50000000000000000000)
  centralHi := (496129665734597241223/100000000000000000000)
  directionLo := (31162758953631157001/6250000000000000000)
  directionHi := (498604143258098512017/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree102.table
  base := (28380123187605657232429774849042185991879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1720)
      previous := (1340)
      next := (0)
      square := (34947014040884580993173713770000000000000)
      linear := (-2982805051681339940095050181620000000000000)
      constant := (64956169244542901808274248356981151485585829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree102.table
  base := (28380117762306336841559883503357189799511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-178200062964854081259957752940000000000000)
      constant := (3938837510306701347579097719150071569398533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31162758953631157001/6250000000000000000)
  centralHi := (498604143258098512017/100000000000000000000)
  directionLo := (501066400915449184913/100000000000000000000)
  directionHi := (250533200457724592457/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree103.table
  base := (3693133402554052628665416526394749659191/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-115263018197180886171906988858260000000000000)
      constant := (2537064307997395853659608074346813963181334746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree103.table
  base := (14772531233447273509675666567802777536687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-810123110174992678844674291470000000000000)
      constant := (18098722970673616022509343012810674993490549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501066400915449184913/100000000000000000000)
  centralHi := (250533200457724592457/50000000000000000000)
  directionLo := (251758308988293814213/50000000000000000000)
  directionHi := (503516617976587628427/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree104.table
  base := (3072749346872775600613249755802775064651/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7803000000000000000000000000000000000000000
      center := (26316)
      previous := (20502)
      next := (0)
      square := (534689314825534089195557820681000000000000)
      linear := (-46573497267020207854071323307822000000000000)
      constant := (1036040766493884896168567310226945053829471753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree104.table
  base := (30727489304161832921998406528503113721623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1636691874016283984039077389420000000000000)
      constant := (36953135486923730840329807223309584070483821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251758308988293814213/50000000000000000000)
  centralHi := (503516617976587628427/100000000000000000000)
  directionLo := (31622185585662211897/6250000000000000000)
  directionHi := (505954969370595390353/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree105.table
  base := (31927401841637984412501982364373172950767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-52268652505742290265977612302600000000000000)
      constant := (1174971688061547707813517788544661540948314989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree105.table
  base := (6385479638680571149755512232315377749881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6000000000000000000000000000000000000000
      center := (20)
      previous := (16)
      next := (0)
      square := (411141341657465658743220162000000000000)
      linear := (-36736389504057391341973471020000000000000)
      constant := (838146805051350319256126831496946133249643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31622185585662211897/6250000000000000000)
  centralHi := (505954969370595390353/100000000000000000000)
  directionLo := (508381625831441071301/100000000000000000000)
  directionHi := (254190812915720535651/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree106.table
  base := (33144792256830401287523329464402008515127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-475100772433159146246883788368580000000000000)
      constant := (10791269814192382543736424590020088872443535981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree106.table
  base := (16572394530598524391345087035604005723981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-834791590674440618369267501190000000000000)
      constant := (19243929080262988661123711893881308154547487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508381625831441071301/100000000000000000000)
  centralHi := (254190812915720535651/50000000000000000000)
  directionLo := (31924797127343279589/6250000000000000000)
  directionHi := (20431870161499698937/4000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree107.table
  base := (8594916159860787183049511256768797267339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-119945918078659420024992266503440000000000000)
      constant := (2752495382317515351186020333565064425077046217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree107.table
  base := (34379661840507966716881412593609285248137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1686028835015179863088263808860000000000000)
      constant := (39266891284759385684209875852587450701699699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31924797127343279589/6250000000000000000)
  centralHi := (20431870161499698937/4000000000000000000)
  directionLo := (513200516745119631577/100000000000000000000)
  directionHi := (256600258372559815789/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree108.table
  base := (35632018921171188556270001419967568576953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-53829619132901801550339371517660000000000000)
      constant := (1247875593028220193371784640634071881956218251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree108.table
  base := (4454002058737602373290313247045563917287/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-47290958018929958039944239315000000000000)
      constant := (1112602933287562502976591300042273383503722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513200516745119631577/100000000000000000000)
  centralHi := (256600258372559815789/50000000000000000000)
  directionLo := (16112283528646618143/3125000000000000000)
  directionHi := (515593072916691780577/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree109.table
  base := (36901855039470548011428133589774330519321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-489149472077594747806139621304120000000000000)
      constant := (11453966237656112931187294643748319101042261763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree109.table
  base := (36901852892862485782850102509239518072203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1718920142347777115787721421820000000000000)
      constant := (40848301099778716356269246138389466987949481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16112283528646618143/3125000000000000000)
  centralHi := (515593072916691780577/100000000000000000000)
  directionLo := (25898728892162655673/5000000000000000000)
  directionHi := (517974577843253113461/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree110.table
  base := (1527566917474614172311597825843484380621/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15606000000000000000000000000000000000000000
      center := (52632)
      previous := (41004)
      next := (0)
      square := (1069378629651068178391115641362000000000000)
      linear := (-98766474391814656331844979789860000000000000)
      constant := (2335847846005594148377665370590483543109928315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree110.table
  base := (38189171057210407955775695261852265195787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1735365796014075742137450228300000000000000)
      constant := (41650677787629855334477164176070011160286249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25898728892162655673/5000000000000000000)
  centralHi := (517974577843253113461/100000000000000000000)
  directionLo := (520345183262145236443/100000000000000000000)
  directionHi := (130086295815536309111/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree111.table
  base := (617093321255378232510095958171388582993/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-13847646440015328208675282683180000000000000)
      constant := (330741647609886311495631437626551002423278896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree111.table
  base := (1974698545728927768944475332327427521773/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1500000000000000000000000000000000000000
      center := (5)
      previous := (4)
      next := (0)
      square := (102785335414366414685805040500000000000)
      linear := (-9732285831557635380484327971000000000000)
      constant := (235893531447776579046518760664982282565319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520345183262145236443/100000000000000000000)
  centralHi := (130086295815536309111/25000000000000000000)
  directionLo := (10454100749396568601/2000000000000000000)
  directionHi := (522705037469828430051/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree112.table
  base := (10204063465208550598728015479799851738861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-125799542930507587341348863559915000000000000)
      constant := (3034086622264251620581710939178238243118332383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree112.table
  base := (20408126209985124926005385524806281815131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-884128551673336497418453920630000000000000)
      constant := (21639387358736796363276501848849769609008537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10454100749396568601/2000000000000000000)
  centralHi := (522705037469828430051/100000000000000000000)
  directionLo := (262527142715069547419/50000000000000000000)
  directionHi := (525054285430139094839/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree113.table
  base := (10539004198185615346969160563117567769629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-126970267900877220804620182971210000000000000)
      constant := (3092045188743876827223282104451553881306415087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree113.table
  base := (42156015531368980482193568236157718232639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1784702757012971621186636647740000000000000)
      constant := (44104494957116835034906504663736258392281253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262527142715069547419/50000000000000000000)
  centralHi := (525054285430139094839/100000000000000000000)
  directionLo := (2109572275512828053/400000000000000000)
  directionHi := (527393068878207013251/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree114.table
  base := (10878315328389084444081919084175521989637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-14237888096805206029765722486945000000000000)
      constant := (350061169760546764337618913736840177565015279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree114.table
  base := (8702652041879905945579469840777467448623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6000000000000000000000000000000000000000
      center := (20)
      previous := (16)
      next := (0)
      square := (411141341657465658743220162000000000000)
      linear := (-40025520237317116611919232316000000000000)
      constant := (998622141743697339551384110994332402345869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2109572275512828053/400000000000000000)
  centralHi := (527393068878207013251/100000000000000000000)
  directionLo := (264860763210121611439/50000000000000000000)
  directionHi := (529721526420243222879/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree115.table
  base := (22443993691747324848711137221630202177687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-258623435683232975462325643587600000000000000)
      constant := (6419205278979561271017269059160255467592491661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree115.table
  base := (4488798641703275112677418232588895134987/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27000000000000000000000000000000000000000
      center := (90)
      previous := (72)
      next := (0)
      square := (1850136037458595464344490729000000000000)
      linear := (-181759406434556887388609426070000000000000)
      constant := (4577927898052244150678695053679900168644649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264860763210121611439/50000000000000000000)
  centralHi := (529721526420243222879/100000000000000000000)
  directionLo := (532039793629397302739/100000000000000000000)
  directionHi := (26601989681469865137/5000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree116.table
  base := (11570048741300818833250718789699065202103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-130482442811986121194434141205095000000000000)
      constant := (3269201523605587543496704159370161805772009709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree116.table
  base := (23140097059664113083378522959603842019983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-917019859005933750117911533590000000000000)
      constant := (23314171381170813708002345852229303734539541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532039793629397302739/100000000000000000000)
  centralHi := (26601989681469865137/5000000000000000000)
  directionLo := (267174001568935830581/50000000000000000000)
  directionHi := (534348003137871661163/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree117.table
  base := (5961235502936166309538603959543763008053/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-14628129753595083850856162290710000000000000)
      constant := (369927464458187676015160086804776385055963902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree117.table
  base := (149030885260030612500655745807784329019/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1500000000000000000000000000000000000000
      center := (5)
      previous := (4)
      next := (0)
      square := (102785335414366414685805040500000000000)
      linear := (-10280474287100922925475288187000000000000)
      constant := (263806598461282676214329632010773647792912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267174001568935830581/50000000000000000000)
  centralHi := (534348003137871661163/100000000000000000000)
  directionLo := (13416157118136748107/2500000000000000000)
  directionHi := (536646284725469924281/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree118.table
  base := (24558527262544451500407205645293531713061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39015000000000000000000000000000000000000000
      center := (131580)
      previous := (102510)
      next := (0)
      square := (2673446574127670445977789103405000000000000)
      linear := (-265647785505450776241953560055370000000000000)
      constant := (6780079217958391361694048644247345427957014983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree118.table
  base := (1227926346931740737806496144692828346447/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13500000000000000000000000000000000000000
      center := (45)
      previous := (36)
      next := (0)
      square := (925068018729297732172245364500000000000)
      linear := (-93346551267223237646764034007000000000000)
      constant := (2417490693087109648720465670541412730708138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13416157118136748107/2500000000000000000)
  centralHi := (536646284725469924281/100000000000000000000)
  directionLo := (269467382702373352793/50000000000000000000)
  directionHi := (538934765404746705587/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree119.table
  base := (50561706438463978162611670206309310931737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4590000000000000000000000000000000000000000
      center := (15480)
      previous := (12060)
      next := (0)
      square := (314523126367961228938563423930000000000000)
      linear := (-31528145346610593313940729279760000000000000)
      constant := (812065602378961070909829731918525973717667283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree119.table
  base := (25280852935798533151319799785048374434141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-941688339505381689642504743310000000000000)
      constant := (24611110588833986676343704511116306109721807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269467382702373352793/50000000000000000000)
  centralHi := (538934765404746705587/100000000000000000000)
  directionLo := (541213569502916841271/100000000000000000000)
  directionHi := (67651696187864605159/12500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree120.table
  base := (52023839733624760906744152605553772969189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-60073485641539846687786408377900000000000000)
      constant := (1561362125981934712440995818065015121164286863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree120.table
  base := (52023839237628973267178308213746222080759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (100)
      previous := (80)
      next := (0)
      square := (2055706708287328293716100810000000000000)
      linear := (-211091370297451333959415365900000000000000)
      constant := (5566934407781890917733445468641238666242277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541213569502916841271/100000000000000000000)
  centralHi := (67651696187864605159/12500000000000000000)
  directionLo := (271741409370336779337/50000000000000000000)
  directionHi := (21739312749626942347/4000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree121.table
  base := (53503454381974098428459217386272056247813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-545344270655337154043162953046280000000000000)
      constant := (14301590115878861759558183189885990854901684839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree121.table
  base := (53503453948018786931950516640270249066361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-1916267986343360631984467099580000000000000)
      constant := (50990379338110970481354126710327296724791747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271741409370336779337/50000000000000000000)
  centralHi := (21739312749626942347/4000000000000000000)
  directionLo := (17054457259626780167/3125000000000000000)
  directionHi := (109148526461611393069/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree122.table
  base := (55000550356171138041182871754649076559677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-550027170536815687896248230691460000000000000)
      constant := (14553108186353345574721431058747366744395159631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree122.table
  base := (27500274988260894696062329992785991035569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-966356820004829629167097953030000000000000)
      constant := (25943065090590611317258154624285221757960363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17054457259626780167/3125000000000000000)
  centralHi := (109148526461611393069/20000000000000000000)
  directionLo := (54799312693750666617/10000000000000000000)
  directionHi := (547993126937506666171/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree123.table
  base := (14128781907502932625974170810164884637067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-15408613067174839493037041898240000000000000)
      constant := (411300370696010913359195531683490454980337089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree123.table
  base := (226060509191577965376994427731515334033/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3000000000000000000000000000000000000000
      center := (10)
      previous := (8)
      next := (0)
      square := (205570670828732829371610081000000000000)
      linear := (-21657325485288420940932496806000000000000)
      constant := (586551802206291116754381658743863650052475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54799312693750666617/10000000000000000000)
  centralHi := (547993126937506666171/100000000000000000000)
  directionLo := (550234416974225201073/100000000000000000000)
  directionHi := (275117208487112600537/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree124.table
  base := (7255898272290426851655221306213751584833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-139848242574943188900604696495455000000000000)
      constant := (3765676397947895741244449520984711807232903798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree124.table
  base := (2902359294390313897619067492999825595263/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13500000000000000000000000000000000000000
      center := (45)
      previous := (36)
      next := (0)
      square := (925068018729297732172245364500000000000)
      linear := (-98280247367112825551682675951000000000000)
      constant := (2685048769480448875045891980982995291072101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550234416974225201073/100000000000000000000)
  centralHi := (275117208487112600537/50000000000000000000)
  directionLo := (276233307221986156887/50000000000000000000)
  directionHi := (22098664577758892551/4000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree125.table
  base := (14899181494218275885523590739155258049/2500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3901500000000000000000000000000000000000000
      center := (13158)
      previous := (10251)
      next := (0)
      square := (267344657412767044597778910340500000000000)
      linear := (-28203793509062564472775203181350000000000000)
      constant := (766039246318491252283393055405963195711269400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree125.table
  base := (29798362861380858970730572196137355831281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 135000000000000000000000000000000000000000
      center := (450)
      previous := (360)
      next := (0)
      square := (9250680187292977321722453645000000000000)
      linear := (-991025300504277568691691162750000000000000)
      constant := (27310034876837588484580056574295708607444587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276233307221986156887/50000000000000000000)
  centralHi := (22098664577758892551/4000000000000000000)
  directionLo := (554689829118403783553/100000000000000000000)
  directionHi := (277344914559201891777/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree126.table
  base := (61163747002285833727695791957982078425251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (29240)
      previous := (22780)
      next := (0)
      square := (594099238695037876883953134090000000000000)
      linear := (-63195418895858869256509926808020000000000000)
      constant := (1731227927623191587444758035608210461994692617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree126.table
  base := (955683543438002318435539973426981563707/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-55513784852079271214808642555000000000000)
      constant := (1542970702504197917040766866764495115057936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554689829118403783553/100000000000000000000)
  centralHi := (277344914559201891777/50000000000000000000)
  directionLo := (139226042144515662321/25000000000000000000)
  directionHi := (111380833715612529857/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree127.table
  base := (62748249231973161960831757645584847533897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 78030000000000000000000000000000000000000000
      center := (263160)
      previous := (205020)
      next := (0)
      square := (5346893148255340891955578206810000000000000)
      linear := (-573441669944208357161674618917360000000000000)
      constant := (15843504858332023065060582539599288565306998291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree127.table
  base := (62748249037595331442610471659148441545499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-2014941908341152390082839938460000000000000)
      constant := (56481601998442221212565021546557007921728473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139226042144515662321/25000000000000000000)
  centralHi := (111380833715612529857/20000000000000000000)
  directionLo := (55910973827312510311/10000000000000000000)
  directionHi := (559109738273125103111/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree128.table
  base := (251368096265898312278955742965884328267/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 19507500000000000000000000000000000000000000
      center := (65790)
      previous := (51255)
      next := (0)
      square := (1336723287063835222988894551702500000000000)
      linear := (-144531142456421722753689974140635000000000000)
      constant := (4027036363842276961538787174032178906461913664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree128.table
  base := (64350232474082138802185621616712119859127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270000000000000000000000000000000000000000
      center := (900)
      previous := (720)
      next := (0)
      square := (18501360374585954643444907290000000000000)
      linear := (-2031387562007451016432568744940000000000000)
      constant := (57424039877971499101610308080611227236196429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell025.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55910973827312510311/10000000000000000000)
  centralHi := (559109738273125103111/100000000000000000000)
  directionLo := (280653320790999053197/50000000000000000000)
  directionHi := (112261328316399621279/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 67
  qDenominator := 153
  table := BinomialMassData.Q67_153.Degree129.table
  base := (16492424304344648012009521208638429129529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (7310)
      previous := (5695)
      next := (0)
      square := (148524809673759469220988283522500000000000)
      linear := (-16189096380754595135217921505770000000000000)
      constant := (454860364987627035894830975539137018055301643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q67_153.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 4
  qDenominator := 9
  table := BinomialMassData.Q4_9.Degree129.table
  base := (8246212133591169679981389844723040129631/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7500000000000000000000000000000000000000
      center := (25)
      previous := (20)
      next := (0)
      square := (513926677071832073429025202500000000000)
      linear := (-56884255990937490077286043095000000000000)
      constant := (1621507192449398664697145744208338240777786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4_9.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell025.Kernel129
