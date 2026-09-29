import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell216.Parameters
import ForestUnimodality.BinomialMassData.Q653_1128.Batch000_049
import ForestUnimodality.BinomialMassData.Q653_1128.Batch050_099
import ForestUnimodality.BinomialMassData.Q7_12.Batch000_049
import ForestUnimodality.BinomialMassData.Q7_12.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree000.table
  base := (152328905558190509827909409/10000000000000000000000000)
  polynomial :=
    { denominator := 11280000000000000000000000000000000000000000
      center := (24161)
      previous := (0)
      next := (17575)
      square := (992685270783384312576202998000000000000000)
      linear := (-2930422059577723636891732876800000000000000)
      constant := (171827005469638895085881813352000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree000.table
  base := (152328905558190509827909409/10000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-31174702761465145073316307200000000000000)
      constant := (1827946866698286117934912908000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree001.table
  base := (46159427946803573996538163213180243739311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-191748460285282173943266491684100000000000000)
      constant := (4989744073983131334474692142738183854166623952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree001.table
  base := (45923249201916542768760457051389463597467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-43495264632890127676212443700000000000000)
      constant := (1123936721336017314335530188245847126339208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49300664859163467021/100000000000000000000)
  directionHi := (24650332429581733511/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree002.table
  base := (14126878875188322008150273165732154414469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-245767083770411336952621538158600000000000000)
      constant := (3217809081089867629657218214911648593749954016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree002.table
  base := (873982159572124042796267662209059814711/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-55815826504315110279108580200000000000000)
      constant := (721962773956429747156448082226557937698048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49300664859163467021/100000000000000000000)
  centralHi := (24650332429581733511/50000000000000000000)
  directionLo := (34860834438919814499/50000000000000000000)
  directionHi := (69721668877839628999/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree003.table
  base := (2181312654547552154321670571784167468247/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-299785707255540499961976584633100000000000000)
      constant := (2230228635218718004757526188666057009945327232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree003.table
  base := (8592138796343406602169175967918453867599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-68136388375740092882004716700000000000000)
      constant := (499319866969538100115026342372585785644752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/50000000000000000000)
  centralHi := (69721668877839628999/100000000000000000000)
  directionLo := (85391256382996653193/100000000000000000000)
  directionHi := (42695628191498326597/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree004.table
  base := (10824096676640679977954706705840480308587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-353804330740669662971331631107600000000000000)
      constant := (1716799575207914235557464611850577808080096784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree004.table
  base := (21193621374834080669128819067097330508731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-80456950247165075484900853200000000000000)
      constant := (384560385008077558680799182605167966104772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85391256382996653193/100000000000000000000)
  centralHi := (42695628191498326597/50000000000000000000)
  directionLo := (49300664859163467021/50000000000000000000)
  directionHi := (98601329718326934043/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree005.table
  base := (1665327286842261197979935982339471097561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-407822954225798825980686677582100000000000000)
      constant := (1495864175618326023478856837482081447666351808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree005.table
  base := (12942286779782193200926235144282120559279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-92777512118590058087796989700000000000000)
      constant := (336071088057466823021071713043885446711348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49300664859163467021/50000000000000000000)
  centralHi := (98601329718326934043/100000000000000000000)
  directionLo := (110239637961024607937/100000000000000000000)
  directionHi := (55119818980512303969/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree006.table
  base := (3960387324118945940787342811558044869697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-461841577710927988990041724056600000000000000)
      constant := (1461204740016235110435960925364347613623712304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree006.table
  base := (7597815182915014199416542519645747132721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-105098073990015040690693126200000000000000)
      constant := (329651141510070495480015018685748965592652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110239637961024607937/100000000000000000000)
  centralHi := (55119818980512303969/50000000000000000000)
  directionLo := (60380736442455994057/50000000000000000000)
  directionHi := (24152294576982397623/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree007.table
  base := (2134132739314326316532354485737592384309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-515860201196057151999396770531100000000000000)
      constant := (1550559440487617009150654290863084645693051888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree007.table
  base := (398440487322568090257271622125096968951/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-117418635861440023293589262700000000000000)
      constant := (351190924833806222913304799867511636274120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60380736442455994057/50000000000000000000)
  centralHi := (24152294576982397623/20000000000000000000)
  directionLo := (13043729868748773229/10000000000000000000)
  directionHi := (130437298687487732291/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree008.table
  base := (837995065217932822531146201104776823133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-569878824681186315008751817005600000000000000)
      constant := (1727394916681835299281739906146341696110438256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree008.table
  base := (1415811130857565226092748639821266881733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-129739197732865005896485399200000000000000)
      constant := (392455501390394468309316965277855202580796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13043729868748773229/10000000000000000000)
  centralHi := (130437298687487732291/100000000000000000000)
  directionLo := (34860834438919814499/25000000000000000000)
  directionHi := (139443337755679257997/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree009.table
  base := (-130490713951827966199025592580414071781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-623897448166315478018106863480100000000000000)
      constant := (1970243398045536066791447507095069785140917008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree009.table
  base := (-15909081800324360906730535331141204321/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-142059759604289988499381535700000000000000)
      constant := (448631376298782671040147312045341777540736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/25000000000000000000)
  centralHi := (139443337755679257997/100000000000000000000)
  directionLo := (18487749322186300133/12500000000000000000)
  directionHi := (29580398915498080213/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree010.table
  base := (-445272285447198076364669685110021500727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-677916071651444641027461909954600000000000000)
      constant := (2266463752433452278670933897658453400469829472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree010.table
  base := (-2025276129962256706552743265642054625597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-154380321475714971102277672200000000000000)
      constant := (516898840465561591700182854062295344492836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18487749322186300133/12500000000000000000)
  centralHi := (29580398915498080213/20000000000000000000)
  directionLo := (31180478223116178213/20000000000000000000)
  directionHi := (77951195557790445533/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree011.table
  base := (-3025170101642657954992365424176425643519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-731934695136573804036816956429100000000000000)
      constant := (2608589360659712097602248029924868868083196696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree011.table
  base := (-654167972662019675175838146281658453157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-166700883347139953705173808700000000000000)
      constant := (595600760405386844737105499735600492810580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31180478223116178213/20000000000000000000)
  centralHi := (77951195557790445533/50000000000000000000)
  directionLo := (163511807252904862237/100000000000000000000)
  directionHi := (81755903626452431119/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree012.table
  base := (-254800236450115447390512787841790414021/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-785953318621702967046172002903600000000000000)
      constant := (2992189173238664241382751969838174230564202624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree012.table
  base := (-2163672453690742479783338148962749283003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-179021445218564936308069945200000000000000)
      constant := (683758379041527465320051767824894017207928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163511807252904862237/100000000000000000000)
  centralHi := (81755903626452431119/50000000000000000000)
  directionLo := (170782512765993306387/100000000000000000000)
  directionHi := (42695628191498326597/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree013.table
  base := (-2492976669367611382873740187429615947059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-839971942106832130055527049378100000000000000)
      constant := (3414614343689622677129209320054169211901440112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree013.table
  base := (-524334028674290467906480362517927786037/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-191342007089989918910966081700000000000000)
      constant := (780789108079185594791626414410348665675560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170782512765993306387/100000000000000000000)
  centralHi := (42695628191498326597/25000000000000000000)
  directionLo := (17775607506417951459/10000000000000000000)
  directionHi := (177756075064179514591/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree014.table
  base := (-1445706514034023047343386315075953382017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-893990565591961293064882095852600000000000000)
      constant := (3874263402437635819093212262950758021995946912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree014.table
  base := (-6048075013817880461245400741646914594039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-203662568961414901513862218200000000000000)
      constant := (886341959369278958029367503150237024871532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17775607506417951459/10000000000000000000)
  centralHi := (177756075064179514591/100000000000000000000)
  directionLo := (184466196843155461033/100000000000000000000)
  directionHi := (92233098421577730517/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree015.table
  base := (-1297200760998127757319813949202006213429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-948009189077090456074237142327100000000000000)
      constant := (4370151213084722570394989700137188442944240680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree015.table
  base := (-270379990464470017168925287525524726807/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-215983130832839884116758354700000000000000)
      constant := (1000201524835743497555899059554842581957900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184466196843155461033/100000000000000000000)
  centralHi := (92233098421577730517/50000000000000000000)
  directionLo := (190940653956493333607/100000000000000000000)
  directionHi := (23867581744561666701/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree016.table
  base := (-1421442978749115877973897224173263539957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1002027812562219619083592188801600000000000000)
      constant := (4901655987630271791445614593385751300828198440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree016.table
  base := (-3694469088094168880301546925987671231843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-228303692704264866719654491200000000000000)
      constant := (1122231920725813335239959932976295890435768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190940653956493333607/100000000000000000000)
  centralHi := (23867581744561666701/12500000000000000000)
  directionLo := (39440531887330773617/20000000000000000000)
  directionHi := (98601329718326934043/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree017.table
  base := (-1913534083218849668599293648598778987377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1056046436047348782092947235276100000000000000)
      constant := (5468370721686968202704027393508404782820883872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree017.table
  base := (-7943815562627946421233538786841124202251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-240624254575689849322550627700000000000000)
      constant := (1252344043378524823491371086770406509572988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39440531887330773617/20000000000000000000)
  centralHi := (98601329718326934043/50000000000000000000)
  directionLo := (203271848627507799433/100000000000000000000)
  directionHi := (101635924313753899717/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree018.table
  base := (-8132040485675683323016331735888637948717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1110065059532477945102302281750600000000000000)
      constant := (6070015895642332980593090335187552970510819528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree018.table
  base := (-4214626922345887684891885905844260988873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-252944816447114831925446764200000000000000)
      constant := (1390476429708743574806100863109737736267048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203271848627507799433/100000000000000000000)
  centralHi := (101635924313753899717/50000000000000000000)
  directionLo := (104582503316759443497/50000000000000000000)
  directionHi := (41833001326703777399/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree019.table
  base := (-8544763358439267900330723428494156154097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1164083683017607108111657328225100000000000000)
      constant := (6706388139786745207835770166362260067334393448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree019.table
  base := (-4424502271985300645938973390010959436949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-265265378318539814528342900700000000000000)
      constant := (1536584061457380268956659415752236973513224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104582503316759443497/50000000000000000000)
  centralHi := (41833001326703777399/20000000000000000000)
  directionLo := (10744830798523022293/5000000000000000000)
  directionHi := (214896615970460445861/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree020.table
  base := (-8895274489627127464968146117964907973691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1218102306502736271121012374699600000000000000)
      constant := (7377330021069157830723855630664472438866797944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree020.table
  base := (-1841199007437663820894117276108968096331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-277585940189964797131239037200000000000000)
      constant := (1690631810103748166939592472433461914220140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10744830798523022293/5000000000000000000)
  centralHi := (214896615970460445861/100000000000000000000)
  directionLo := (1763834207376393727/800000000000000000)
  directionHi := (55119818980512303969/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree021.table
  base := (-4593006372091656148782792368269151114391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1272120929987865434130367421174100000000000000)
      constant := (8082712240625697079579096334926691619038893488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree021.table
  base := (-1187831097730014822075746305956737699871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-289906502061389779734135173700000000000000)
      constant := (1852590594157904991526368675140653180812384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1763834207376393727/800000000000000000)
  centralHi := (55119818980512303969/25000000000000000000)
  directionLo := (28240503566095748121/12500000000000000000)
  directionHi := (225924028528765984969/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree022.table
  base := (-4709542244401514077346770233969086039211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1326139553472994597139722467648600000000000000)
      constant := (8822423127319649926011150588392614869090379248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree022.table
  base := (-9741073363208940250520297502832817090709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-302227063932814762337031310200000000000000)
      constant := (2022435122596455456210153641616006194911492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28240503566095748121/12500000000000000000)
  centralHi := (225924028528765984969/100000000000000000000)
  directionLo := (115620307712596732889/50000000000000000000)
  directionHi := (231240615425193465779/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree023.table
  base := (-4798190411143256016779442289685256284411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1380158176958123760149077514123100000000000000)
      constant := (9596362422657023005376098903960049155651332848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree023.table
  base := (-992317120479211856915611733640812707103/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-314547625804239744939927446700000000000000)
      constant := (2200142566337431547675636774375602475147640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115620307712596732889/50000000000000000000)
  centralHi := (231240615425193465779/100000000000000000000)
  directionLo := (118218841325925895933/50000000000000000000)
  directionHi := (236437682651851791867/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree024.table
  base := (-9719647169021090522914519083568156127137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1434176800443252923158432560597600000000000000)
      constant := (10404437591218497811244617428521950634763704808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree024.table
  base := (-10050705003401908900098106404960122209343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-326868187675664727542823583200000000000000)
      constant := (2385691773019086201511801955940478533487884) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118218841325925895933/50000000000000000000)
  centralHi := (236437682651851791867/100000000000000000000)
  directionLo := (60380736442455994057/25000000000000000000)
  directionHi := (241522945769823976229/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree025.table
  base := (-1223815602483830553717855305658155552249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1488195423928382086167787607072100000000000000)
      constant := (11246561618327634838753727325071974051935736128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree025.table
  base := (-5062668320436945164261990186774561947467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-339188749547089710145719719700000000000000)
      constant := (2579062800059392468696516598329910513260792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60380736442455994057/25000000000000000000)
  centralHi := (241522945769823976229/100000000000000000000)
  directionLo := (123251662147908667553/50000000000000000000)
  directionHi := (246503324295817335107/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree026.table
  base := (-2452643985153469450870226656346355781673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1542214047413511249177142653546600000000000000)
      constant := (12122651684203510314018473846849791407515296928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree026.table
  base := (-1014865054492823022643120670476464942673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-351509311418514692748615856200000000000000)
      constant := (2780236634325708340765811091992824206879240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123251662147908667553/50000000000000000000)
  centralHi := (246503324295817335107/100000000000000000000)
  directionLo := (251385052149972601437/100000000000000000000)
  directionHi := (125692526074986300719/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree027.table
  base := (-9781298827451226542621569870084000420983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1596232670898640412186497700021100000000000000)
      constant := (13032628355174761927444359621077232883681165272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree027.table
  base := (-1012216792257015480391112411605563183443/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-363829873289939675351511992700000000000000)
      constant := (2989195021333971103198589372319832417986840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251385052149972601437/100000000000000000000)
  centralHi := (125692526074986300719/50000000000000000000)
  directionLo := (12808688457449497979/5000000000000000000)
  directionHi := (256173769148989959581/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree028.table
  base := (-2426034350262896814956265628006491564467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1650251294383769575195852746495600000000000000)
      constant := (13976415080343207456214589876437731372872870112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree028.table
  base := (-10047355628030253048277827988992193544951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-376150435161364657954408129200000000000000)
      constant := (3205920358833413688147082294732093677460588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12808688457449497979/5000000000000000000)
  centralHi := (256173769148989959581/100000000000000000000)
  directionLo := (260874597374975464581/100000000000000000000)
  directionHi := (130437298687487732291/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree029.table
  base := (-4790243645107680609069264787531953199637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1704269917868898738205207792970100000000000000)
      constant := (14953937869052364826967457172346718188336089616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree029.table
  base := (-992563186959220081178149247780364997301/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-388470997032789640557304265700000000000000)
      constant := (3430395628324631985384287769378856200323880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260874597374975464581/100000000000000000000)
  centralHi := (130437298687487732291/50000000000000000000)
  directionLo := (26549220536789985223/10000000000000000000)
  directionHi := (265492205367899852231/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree030.table
  base := (-1882339978136044393001553940655399325419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1758288541354027901214562839444600000000000000)
      constant := (15965125075705805538911575047889691746817931480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree030.table
  base := (-9758370047612855358152229945971805615643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-400791558904214623160200402200000000000000)
      constant := (3662604349003343707745444447898338332612284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26549220536789985223/10000000000000000000)
  centralHi := (265492205367899852231/100000000000000000000)
  directionLo := (67507715608415210739/25000000000000000000)
  directionHi := (270030862433660842957/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree031.table
  base := (-229977130400919845890830770721476459147/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1812307164839157064223917885919100000000000000)
      constant := (17009907248623009052291956555493464411674505920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree031.table
  base := (-9546901481798949255103858610785032181213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-413112120775639605763096538700000000000000)
      constant := (3902530545033068064417986511683079613825444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67507715608415210739/25000000000000000000)
  centralHi := (270030862433660842957/100000000000000000000)
  directionLo := (137247242433338366711/50000000000000000000)
  directionHi := (274494484866676733423/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree032.table
  base := (-4471957011398081582057889874800360503329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1866325788324286227233272932393600000000000000)
      constant := (18088217017376783614019910141006368175111019472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree032.table
  base := (-2323129368185141892251850900049929418961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-425432682647064588365992675200000000000000)
      constant := (4150158720806724034605461659197603387889872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137247242433338366711/50000000000000000000)
  centralHi := (274494484866676733423/100000000000000000000)
  directionLo := (34860834438919814499/12500000000000000000)
  directionHi := (278886675511358515993/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree033.table
  base := (-2161854873569312787893891576500832557641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1920344411809415390242627978868100000000000000)
      constant := (19199989003520293297696849940484383694496418976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree033.table
  base := (-8996470959173577365043083884964994114607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-437753244518489570968888811700000000000000)
      constant := (4405473841059481213525707262792920070624716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/12500000000000000000)
  centralHi := (278886675511358515993/100000000000000000000)
  directionLo := (141605378899720237051/50000000000000000000)
  directionHi := (283210757799440474103/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree034.table
  base := (-1662159730324518562715923163726681397829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-1974363035294544553251983025342600000000000000)
      constant := (20345159745780645466937474539532356295063488680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree034.table
  base := (-4329988962405026409984500042698213404561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-450073806389914553571784948200000000000000)
      constant := (4668461313986794711057626115025242878290536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141605378899720237051/50000000000000000000)
  centralHi := (283210757799440474103/100000000000000000000)
  directionLo := (287469805177672336503/100000000000000000000)
  directionHi := (35933725647209042063/12500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree035.table
  base := (-3967606795812522829184122970536746080731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2028381658779673716261338071817100000000000000)
      constant := (21523667634434269988084915257427953989567930608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree035.table
  base := (-1656843729085242817816241086239317438113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-462394368261339536174681084700000000000000)
      constant := (4939106976279349885337665577138140953713220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287469805177672336503/100000000000000000000)
  centralHi := (35933725647209042063/12500000000000000000)
  directionLo := (145833333333333333333/50000000000000000000)
  directionHi := (291666666666666666667/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree036.table
  base := (-7521792610556624235256628368482231112119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2082400282264802879270693118291600000000000000)
      constant := (22735452851726009737792678951580646035359899096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree036.table
  base := (-7870338829830288429885352443269279753453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-474714930132764518777577221200000000000000)
      constant := (5217397079431448009275757818880768642958564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145833333333333333333/50000000000000000000)
  centralHi := (291666666666666666667/100000000000000000000)
  directionLo := (18487749322186300133/6250000000000000000)
  directionHi := (295803989154980802129/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree037.table
  base := (-7071631249288151836493196482988119927623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2136418905749932042280048164766100000000000000)
      constant := (23980457316461057148398922677803508083917139032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree037.table
  base := (-463715667910261961793587546101551685351/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-487035492004189501380473357700000000000000)
      constant := (5503318276940586096316111324861002076412608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18487749322186300133/6250000000000000000)
  centralHi := (295803989154980802129/100000000000000000000)
  directionLo := (74971059231027423321/25000000000000000000)
  directionHi := (59976847384821938657/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree038.table
  base := (-6585793280870432034286627279740225316247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2190437529235061205289403211240600000000000000)
      constant := (25258624631647350817719431216521717214633849048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree038.table
  base := (-6932633935400930657970430267717454659891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-499356053875614483983369494200000000000000)
      constant := (5796857612169488054149289135637390544081308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74971059231027423321/25000000000000000000)
  centralHi := (59976847384821938657/20000000000000000000)
  directionLo := (303909708813507817343/100000000000000000000)
  directionHi := (2374294600105529823/781250000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree039.table
  base := (-6065311653402779361118290983935262164679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2244456152720190368298758257715100000000000000)
      constant := (26569900034508457486500172243876244391077378136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree039.table
  base := (-3205468387588233013059342631394507913607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-511676615747039466586265630700000000000000)
      constant := (6098002506732122365314320320459031810073432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303909708813507817343/100000000000000000000)
  centralHi := (2374294600105529823/781250000000000000)
  directionLo := (30788255336518609993/10000000000000000000)
  directionHi := (307882553365186099931/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree040.table
  base := (-551118939607733703436285708459726786637/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2298474776205319531308113304189600000000000000)
      constant := (27914230348448726489928810282236991246796528080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree040.table
  base := (-1463844203766307561995005622564840333427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-523997177618464449189161767200000000000000)
      constant := (6406740749318395836753150598116887663995504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30788255336518609993/10000000000000000000)
  centralHi := (307882553365186099931/100000000000000000000)
  directionLo := (311804782231161782131/100000000000000000000)
  directionHi := (77951195557790445533/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree041.table
  base := (-307775030835128757474991334146836048959/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2352493399690448694317468350664100000000000000)
      constant := (29291563936707604722248580663506697690454234496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree041.table
  base := (-658367746724511309498438987165921843491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-536317739489889431792057903700000000000000)
      constant := (6723060484903562062636583129244571503024864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311804782231161782131/100000000000000000000)
  centralHi := (77951195557790445533/25000000000000000000)
  directionLo := (39459785260157939407/12500000000000000000)
  directionHi := (315678282081263515257/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree042.table
  base := (-17223562922191950002953088030589260431/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2406512023175577857326823397138600000000000000)
      constant := (30701850657532102465990165527555394942247526000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree042.table
  base := (-1161647837440203826690873202608178935439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-548638301361314414394954040200000000000000)
      constant := (7046950204306919819805149841924807411098928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39459785260157939407/12500000000000000000)
  centralHi := (315678282081263515257/100000000000000000000)
  directionLo := (79876206302836724879/25000000000000000000)
  directionHi := (319504825211346899517/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree043.table
  base := (-3656578512851311682705880726346790355931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2460530646660707020336178443613100000000000000)
      constant := (32145041820751278059312313071850204812489962104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree043.table
  base := (-998814016012510254125797582211543395089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-560958863232739396997850176700000000000000)
      constant := (7378398734075381472944508034966345917035728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79876206302836724879/25000000000000000000)
  centralHi := (319504825211346899517/100000000000000000000)
  directionLo := (323286079021180386007/100000000000000000000)
  directionHi := (40410759877647548251/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree044.table
  base := (-1488677829820359500749125865135862809053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2514549270145836183345533490087600000000000000)
      constant := (33621090145669481227425882463288814194630492304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree044.table
  base := (-3313840077903803593655200450524412061033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-573279425104164379600746313200000000000000)
      constant := (7717395226674066590193274556393707055267604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323286079021180386007/100000000000000000000)
  centralHi := (40410759877647548251/12500000000000000000)
  directionLo := (13080944580232388979/4000000000000000000)
  directionHi := (81755903626452431119/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree045.table
  base := (-2269088174985961431404805046650897922729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2568567893630965346354888536562100000000000000)
      constant := (35129949720214949999661945809707662245728599336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree045.table
  base := (-2603220985733033086348683027932848657257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-585599986975589362203642449700000000000000)
      constant := (8063929150970044010973899487977305816112916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13080944580232388979/4000000000000000000)
  centralHi := (81755903626452431119/25000000000000000000)
  directionLo := (82679728470768455953/25000000000000000000)
  directionHi := (330718913883073823813/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree046.table
  base := (-766308497747230366254211830799285674117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2622586517116094509364243583036600000000000000)
      constant := (36671575961292505303987948986714915141402026256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree046.table
  base := (-1864250784665722645245726699032100370083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-597920548847014344806538586200000000000000)
      constant := (8417990282997777817478437766061614795559004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82679728470768455953/25000000000000000000)
  centralHi := (330718913883073823813/100000000000000000000)
  directionLo := (167186688731157328609/50000000000000000000)
  directionHi := (334373377462314657219/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree047.table
  base := (-768758716259735273130316643446585735881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11280000000000000000000000000000000000000000
      center := (24161)
      previous := (0)
      next := (17575)
      square := (992685270783384312576202998000000000000000)
      linear := (-56949045544706886646246779351300000000000000)
      constant := (813743097368014237672105846262636001289926232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree047.table
  base := (-1097756621444303099730603979747449521911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-610241110718439327409434722700000000000000)
      constant := (8779568696996358839754278120455530605737068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167186688731157328609/50000000000000000000)
  centralHi := (334373377462314657219/100000000000000000000)
  directionLo := (168994164922277058417/50000000000000000000)
  directionHi := (67597665968910823367/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree048.table
  base := (10846852173208598955995186419377185799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2730623764086352835382953675985600000000000000)
      constant := (39852956525746402370013713233531219401764639568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree048.table
  base := (-60908303483642037806514685407068942847/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-622561672589864310012330859200000000000000)
      constant := (9148654756709593848930669448475575863429180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168994164922277058417/50000000000000000000)
  centralHi := (67597665968910823367/20000000000000000000)
  directionLo := (170782512765993306387/50000000000000000000)
  directionHi := (13662601021279464511/4000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree049.table
  base := (83797026036744610025041405561765840269/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2784642387571481998392308722460100000000000000)
      constant := (41492627987005912416693370058366682027877013040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree049.table
  base := (128653731920107873848744234307724760993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-634882234461289292615226995700000000000000)
      constant := (9525239106940697349910171093859270788527664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170782512765993306387/50000000000000000000)
  centralHi := (13662601021279464511/4000000000000000000)
  directionLo := (345104654014144269149/100000000000000000000)
  directionHi := (6902093080282885383/2000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree050.table
  base := (167932323381393127053978421931886441533/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2838661011056611161401663768934600000000000000)
      constant := (43164900319058272211248037706292033915843135280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree050.table
  base := (135895585253035198813393309542886245659/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-647202796332714275218123132200000000000000)
      constant := (9909312665353814103107765688395146349479080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345104654014144269149/100000000000000000000)
  centralHi := (6902093080282885383/2000000000000000000)
  directionLo := (34860834438919814499/10000000000000000000)
  directionHi := (348608344389198144991/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree051.table
  base := (636256637369670275590306954087044061903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2892679634541740324411018815409100000000000000)
      constant := (44869735028300297283471813203816021161943397792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree051.table
  base := (1113873235483508146860076618446868710967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-659523358204139257821019268700000000000000)
      constant := (10300866614514969688577883530355224849063208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/10000000000000000000)
  centralHi := (348608344389198144991/100000000000000000000)
  directionLo := (70415433914258693101/20000000000000000000)
  directionHi := (176038584785646732753/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree052.table
  base := (686875029689086762837805243928216620007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-2946698258026869487420373861883600000000000000)
      constant := (46607094735328483098755329052206191661631455560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree052.table
  base := (124810937123556842269769079024990568191/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-671843920075564240423915405200000000000000)
      constant := (10699892394165346066055611695107497170457300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70415433914258693101/20000000000000000000)
  centralHi := (176038584785646732753/50000000000000000000)
  directionLo := (355512150128359029181/100000000000000000000)
  directionHi := (177756075064179514591/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree053.table
  base := (4346684379742942501980226316018699255447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3000716881511998650429728908358100000000000000)
      constant := (48376943142686938031233844049214253609726778152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree053.table
  base := (1008961043788437212110173749438475797321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-684164481946989223026811541700000000000000)
      constant := (11106381693720035426395764670885546838271408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355512150128359029181/100000000000000000000)
  centralHi := (177756075064179514591/50000000000000000000)
  directionLo := (1794571288946502429/500000000000000000)
  directionHi := (358914257789300485801/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree054.table
  base := (1056257881922997790161995769899068932083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3054735504997127813439083954832600000000000000)
      constant := (50179245003549242416024902386684870192516561640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree054.table
  base := (2486893181356433711580817703731612520883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-696485043818414205629707678200000000000000)
      constant := (11520326444985654182650567394939558700501192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1794571288946502429/500000000000000000)
  centralHi := (358914257789300485801/100000000000000000000)
  directionLo := (181142209327367982171/50000000000000000000)
  directionHi := (362284418654735964343/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree055.table
  base := (6237544647893905384415746618089518097903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3108754128482256976448439001307100000000000000)
      constant := (52013966091307067178302169392317790141478425448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree055.table
  base := (1483361812862539359862167985723311550207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-708805605689839188232603814700000000000000)
      constant := (11941718815090408902722519352127218954409936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181142209327367982171/50000000000000000000)
  centralHi := (362284418654735964343/100000000000000000000)
  directionLo := (365623516141338419183/100000000000000000000)
  directionHi := (22851469758833651199/6250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree056.table
  base := (450926449436313970004924469363539249383/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3162772751967386139457794047781600000000000000)
      constant := (53881073170039225320389028446368038349524626048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree056.table
  base := (6914193140207554215859287627357135662747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-721126167561264170835499951200000000000000)
      constant := (12370551199620402810434310338728285627952964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365623516141338419183/100000000000000000000)
  centralHi := (22851469758833651199/6250000000000000000)
  directionLo := (184466196843155461033/50000000000000000000)
  directionHi := (368932393686310922067/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree057.table
  base := (1026564535119054793765324462991091064549/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3216791375452515302467149094256100000000000000)
      constant := (55780533965835623094398501280050841721025038272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree057.table
  base := (7915408810695270414292129845933182180219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-733446729432689153438396087700000000000000)
      constant := (12806816215956158457728724123363698186162628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184466196843155461033/50000000000000000000)
  centralHi := (368932393686310922067/100000000000000000000)
  directionLo := (46526482154431863587/12500000000000000000)
  directionHi := (372211857235454908697/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree058.table
  base := (9230032780322765021491267842354155926647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3270809998937644465476504140730600000000000000)
      constant := (57712317138951335336960976757126672930607117352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree058.table
  base := (8936496988399592884815238847263890661709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-745767291304114136041292224200000000000000)
      constant := (13250506696803511286806577189017166687940508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46526482154431863587/12500000000000000000)
  centralHi := (372211857235454908697/100000000000000000000)
  directionLo := (1877313387678134989/500000000000000000)
  directionHi := (375462677535626997801/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree059.table
  base := (5133399331006650452068480153204120555437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3324828622422773628485859187205100000000000000)
      constant := (59676392256766757549441838188243345560734095984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree059.table
  base := (1995375563843104127371336404559198861007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-758087853175539118644188360700000000000000)
      constant := (13701615683913201285781006344386051931660420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1877313387678134989/500000000000000000)
  centralHi := (375462677535626997801/100000000000000000000)
  directionLo := (47335699031257347407/12500000000000000000)
  directionHi := (378685592250058779257/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree060.table
  base := (1132225651408425672804103099683651345501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3378847245907902791495214233679600000000000000)
      constant := (61672729767530489863901777243866784597330810160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree060.table
  base := (2207197672269079394344999898680159066473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-770408415046964101247084497200000000000000)
      constant := (14160136421983656574267714070920809543988380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47335699031257347407/12500000000000000000)
  centralHi := (378685592250058779257/100000000000000000000)
  directionLo := (76376261582597333443/20000000000000000000)
  directionHi := (23867581744561666701/6250000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree061.table
  base := (12395865058803539354839780135174506607027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3432865869393031954504569280154100000000000000)
      constant := (63701300974862287630517304016541917892278143432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree061.table
  base := (12113282092018130039269659508282145370989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-782728976918389083849980633700000000000000)
      constant := (14626062352741624050064893987611885744451868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76376261582597333443/20000000000000000000)
  centralHi := (23867581744561666701/6250000000000000000)
  directionLo := (385050501738264053503/100000000000000000000)
  directionHi := (1504103522415093959/390625000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree062.table
  base := (13487098685636987396186857780964683453363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3486884492878161117513924326628600000000000000)
      constant := (65762078012994071749123848417825448657963492808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree062.table
  base := (6604114214298311076548970758490866613291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-795049538789814066452876770200000000000000)
      constant := (15099387109195458540935833447853780798718984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385050501738264053503/100000000000000000000)
  centralHi := (1504103522415093959/390625000000000000)
  directionLo := (194096911647535265751/50000000000000000000)
  directionHi := (388193823295070531503/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree063.table
  base := (729772349887850156628463486276087348161/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3540903116363290280523279373103100000000000000)
      constant := (67855033822727630299023709546749717187002071520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree063.table
  base := (14320312263653660963387369340738281218031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-807370100661239049055772906700000000000000)
      constant := (15580104510056033498682662737501359374616372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194096911647535265751/50000000000000000000)
  centralHi := (388193823295070531503/100000000000000000000)
  directionLo := (391311896062463196871/100000000000000000000)
  directionHi := (48913987007807899609/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree064.table
  base := (125763314973425663844713623032074085509/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3594921739848419443532634419577600000000000000)
      constant := (69980142128088262449239468944543954964668143000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree064.table
  base := (7724516756804391086431296857535442832301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-819690662532664031658669043200000000000000)
      constant := (16068208554320383351738077665380850627975224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391311896062463196871/100000000000000000000)
  centralHi := (48913987007807899609/12500000000000000000)
  directionLo := (394405318873307736171/100000000000000000000)
  directionHi := (98601329718326934043/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree065.table
  base := (8430759764820044300748237459255754541501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3648940363333548606541989466052100000000000000)
      constant := (72137377413654216824603946945176462415544434032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree065.table
  base := (4148476670132627033122758215708103853103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-832011224404089014261565179700000000000000)
      constant := (16563693416013330368313687250166488984948944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394405318873307736171/100000000000000000000)
  centralHi := (98601329718326934043/25000000000000000000)
  directionLo := (198737333628530343573/50000000000000000000)
  directionHi := (397474667257060687147/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree066.table
  base := (3603659024873521798059866021751495464647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3702958986818677769551344512526600000000000000)
      constant := (74326714902542360116276500626586111417768626760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree066.table
  base := (8877230213359955902369330716774377793573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-844331786275513996864461316200000000000000)
      constant := (17066553439082487423959083187652585067045752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198737333628530343573/50000000000000000000)
  centralHi := (397474667257060687147/100000000000000000000)
  directionLo := (40052049468993052599/10000000000000000000)
  directionHi := (400520494689930525991/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree067.table
  base := (19190287335851451515433927073951350548377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3756977610303806932560699559001100000000000000)
      constant := (76548130535031078340702141374393711050672755032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree067.table
  base := (1183139822606416406187404995433830703649/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-856652348146938979467357452700000000000000)
      constant := (17576783132442162550386981483835795495100608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40052049468993052599/10000000000000000000)
  centralHi := (400520494689930525991/100000000000000000000)
  directionLo := (4035433337601083731/1000000000000000000)
  directionHi := (403543333760108373101/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree068.table
  base := (20377055479799926968044804279785532976777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3810996233788936095570054605475600000000000000)
      constant := (78801600947801963302784188039896409816296809432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree068.table
  base := (20120792641267588935881428214321741212433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-868972910018363962070253589200000000000000)
      constant := (18094377165161821692244713417171860894549196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4035433337601083731/1000000000000000000)
  centralHi := (403543333760108373101/100000000000000000000)
  directionLo := (406543697255015598867/100000000000000000000)
  directionHi := (101635924313753899717/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree069.table
  base := (21578171627424669667622307266130156549987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3865014857274065258579409651950100000000000000)
      constant := (81087103453782371007604740782235962629654110792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree069.table
  base := (1332855973637522280070560993096620052693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-881293471889788944673149725700000000000000)
      constant := (18619330361794892833921176622787051050117056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406543697255015598867/100000000000000000000)
  centralHi := (101635924313753899717/25000000000000000000)
  directionLo := (409522079176853825141/100000000000000000000)
  directionHi := (204761039588426912571/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree070.table
  base := (911728809449280701064014430545487075499/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3919033480759194421588764698424600000000000000)
      constant := (83404616022571457465929396554932613569866374600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree070.table
  base := (2254452726437110826185317981791935642229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-893614033761213927276045862200000000000000)
      constant := (19151637697843817692941715783065032277067480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409522079176853825141/100000000000000000000)
  centralHi := (204761039588426912571/50000000000000000000)
  directionLo := (412478955692152722567/100000000000000000000)
  directionHi := (51559869461519090321/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree071.table
  base := (1501362361968842331114180381072147002913/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-3973052104244323584598119744899100000000000000)
      constant := (85754117261432801007767140754944491378102969728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree071.table
  base := (11888440601922436716247503452373820087231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-905934595632638909878941998700000000000000)
      constant := (19691294295357376619159622500869471682093544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412478955692152722567/100000000000000000000)
  centralHi := (51559869461519090321/12500000000000000000)
  directionLo := (103853696505120980589/25000000000000000000)
  directionHi := (415414786020483922357/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree072.table
  base := (12631756229070950150275797778361003727587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4027070727729452747607474791373600000000000000)
      constant := (88135586396837209294659316129040373947243504784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree072.table
  base := (6255590689173302219506616894145836644303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-918255157504063892481838135200000000000000)
      constant := (20238295418656428295194560901319000158926544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103853696505120980589/25000000000000000000)
  centralHi := (415414786020483922357/100000000000000000000)
  directionLo := (418330013267037773989/100000000000000000000)
  directionHi := (41833001326703777399/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree073.table
  base := (26517983742624951752845690913522408576757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4081089351214581910616829837848100000000000000)
      constant := (90549003256539784129807185510321260263105349112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree073.table
  base := (26280588793194921629038625559201283594247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-930575719375488875084734271700000000000000)
      constant := (20792636470184318405413623749122915403130964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418330013267037773989/100000000000000000000)
  centralHi := (41833001326703777399/10000000000000000000)
  directionLo := (421225065203337057487/100000000000000000000)
  directionHi := (26326566575208566093/6250000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree074.table
  base := (27784842164704155190563844721584260470229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4135107974699711073626184884322600000000000000)
      constant := (92994348252175778316987620218911536153089660664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree074.table
  base := (27551187358122826458221876876284926589909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-942896281246913857687630408200000000000000)
      constant := (21354312986478320727089095796565419119078908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421225065203337057487/100000000000000000000)
  centralHi := (26326566575208566093/6250000000000000000)
  directionLo := (106025088749995604257/25000000000000000000)
  directionHi := (424100354999982417029/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree075.table
  base := (29063728938636239850122510651561666145533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4189126598184840236635539930797100000000000000)
      constant := (95471602362360226613398474962614599542371577528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree075.table
  base := (14416898672411167262342466514476078513449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-955216843118338840290526544700000000000000)
      constant := (21923320634258580194130281581659925884322776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106025088749995604257/25000000000000000000)
  centralHi := (424100354999982417029/100000000000000000000)
  directionLo := (426956281914983265967/100000000000000000000)
  directionHi := (26684767619686454123/6250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree076.table
  base := (3794286957953715079624634327083698964467/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4243145221669969399644894977271600000000000000)
      constant := (97980747116276767645268432801005455074401459776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree076.table
  base := (15064034089398126145110283436524239784241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-967537404989763822893422681200000000000000)
      constant := (22499655206631130484078694378676581754821784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426956281914983265967/100000000000000000000)
  centralHi := (26684767619686454123/6250000000000000000)
  directionLo := (429793231940920891721/100000000000000000000)
  directionHi := (214896615970460445861/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree077.table
  base := (3957025502906700560376754285856088519689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4297163845155098562654250023746100000000000000)
      constant := (100521764577741495884095207334553677361678656192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree077.table
  base := (15716829755259251390828473944955535634781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-979857966861188805496318817700000000000000)
      constant := (23083312619401658673256272221391432855234744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429793231940920891721/100000000000000000000)
  centralHi := (214896615970460445861/50000000000000000000)
  directionLo := (54076447301739209001/12500000000000000000)
  directionHi := (432611578413913672009/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree078.table
  base := (6593825098709370079284048790655265905751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4351182468640227725663605070220600000000000000)
      constant := (103094637329728092780660013790360322886296475080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree078.table
  base := (32750240917207570927919157744712780024821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-992178528732613788099214954200000000000000)
      constant := (23674288907496786580810116089786553360297852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54076447301739209001/12500000000000000000)
  centralHi := (432611578413913672009/100000000000000000000)
  directionLo := (54426460323388047181/12500000000000000000)
  directionHi := (435411682587104377449/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree079.table
  base := (34292741059576720013246734914483115385259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4405201092125356888672960116695100000000000000)
      constant := (105699348459340884277858673323748293095264891144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree079.table
  base := (34077491613298328258618437649045069439427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1004499090604038770702111090700000000000000)
      constant := (24272580221489732665095560878401040833273124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54426460323388047181/12500000000000000000)
  centralHi := (435411682587104377449/100000000000000000000)
  directionLo := (438193894171163559001/100000000000000000000)
  directionHi := (219096947085581779501/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree080.table
  base := (8906685235050361864312168046468970901381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4459219715610486051682315163169600000000000000)
      constant := (108335881543222858515996189763174395845230460384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree080.table
  base := (8853775042339629151385570158155207564081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1016819652475463753305007227200000000000000)
      constant := (24878182824227309828094056503591449963075888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438193894171163559001/100000000000000000000)
  centralHi := (219096947085581779501/50000000000000000000)
  directionLo := (1763834207376393727/400000000000000000)
  directionHi := (440958551844098431751/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree081.table
  base := (18485412160399869055816138060847408163817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4513238339095615214691670209644100000000000000)
      constant := (111004220633386052939668624086939028632425844144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree081.table
  base := (7352552847840714458269074667434808110633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1029140214346888735907903363700000000000000)
      constant := (25491093087555303305677459205058588486637980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1763834207376393727/400000000000000000)
  centralHi := (440958551844098431751/100000000000000000000)
  directionLo := (55463247966558900399/12500000000000000000)
  directionHi := (443705983732471203193/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree082.table
  base := (9581174773434120404882688415285157092509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4567256962580744377701025256118600000000000000)
      constant := (113704350243452084538196326394130856553665828576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree082.table
  base := (38120190294970658118133861931360579261367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1041460776218313718510799500200000000000000)
      constant := (26111307489139359051471042736826326951136404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55463247966558900399/12500000000000000000)
  centralHi := (443705983732471203193/100000000000000000000)
  directionLo := (44643650786596245343/10000000000000000000)
  directionHi := (446436507865962453431/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree083.table
  base := (496101020079259262566421077844734977229/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4621275586065873540710380302593100000000000000)
      constant := (116436255335290950916879274413491023814221813120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree083.table
  base := (39487093369919746590211967727910739109497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1053781338089738701113695636700000000000000)
      constant := (26738822609378596735526457754647428869313964) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44643650786596245343/10000000000000000000)
  centralHi := (446436507865962453431/100000000000000000000)
  directionLo := (22457521630353109331/5000000000000000000)
  directionHi := (449150432607062186621/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree084.table
  base := (10265174104044640754197269921590007522967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4675294209551002703719735349067600000000000000)
      constant := (119199921306046573610099257383976963355350473888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree084.table
  base := (20431598404368185171887063237177754626303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1066101899961163683716591773200000000000000)
      constant := (27373635128409242749478037487492266111031272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22457521630353109331/5000000000000000000)
  centralHi := (449150432607062186621/100000000000000000000)
  directionLo := (451848057057531969937/100000000000000000000)
  directionHi := (225924028528765984969/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree085.table
  base := (42442276053409450233492714502193384382141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4729312833036131866729090395542100000000000000)
      constant := (121995333975537888806612944242705690716403587256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree085.table
  base := (67597171240187569050929392395396586721/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1078422461832588666319487909700000000000000)
      constant := (28015741823195657508661908320277974400407500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451848057057531969937/100000000000000000000)
  centralHi := (225924028528765984969/50000000000000000000)
  directionLo := (90905934288630953429/20000000000000000000)
  directionHi := (227264835721577383573/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree086.table
  base := (43832560790021448610449414102846710940531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4783331456521261029738445442016600000000000000)
      constant := (124822479574024614750771931028523746227223191496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree086.table
  base := (21820969133213118973313959065514603017849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1090743023704013648922384046200000000000000)
      constant := (28665139564706207938085018882022350472428376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90905934288630953429/20000000000000000000)
  centralHi := (227264835721577383573/50000000000000000000)
  directionLo := (45719555747817342257/10000000000000000000)
  directionHi := (457195557478173422571/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree087.table
  base := (45231298415745740214163941682665085402969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4837350080006390192747800488491100000000000000)
      constant := (127681344730327139791014034266942528417723804504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree087.table
  base := (45044062385214754932157686461642211456189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1103063585575438631525280182700000000000000)
      constant := (29321825315171510390375278168752206537474268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45719555747817342257/10000000000000000000)
  centralHi := (457195557478173422571/100000000000000000000)
  directionLo := (459845988710713158193/100000000000000000000)
  directionHi := (229922994355356579097/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree088.table
  base := (23319122010228697544528331282292339857107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4891368703491519355757155534965600000000000000)
      constant := (130571916460290280640814244045922821379728769424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree088.table
  base := (46454358617405829085284584383327449787491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1115384147446863614128176319200000000000000)
      constant := (29985796125422641435195059090199929397449892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459845988710713158193/100000000000000000000)
  centralHi := (229922994355356579097/50000000000000000000)
  directionLo := (462481230850386931557/100000000000000000000)
  directionHi := (231240615425193465779/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree089.table
  base := (48053159782874533450157784109327260483321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4945387326976648518766510581440100000000000000)
      constant := (133494182155580957161492601838900650291783746136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree089.table
  base := (2992036772934252587234717763966125723781/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1127704709318288596731072455700000000000000)
      constant := (30657049132306984044421324114293996138965952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462481230850386931557/100000000000000000000)
  centralHi := (231240615425193465779/50000000000000000000)
  directionLo := (93020308415838838143/20000000000000000000)
  directionHi := (116275385519798547679/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree090.table
  base := (49475814765373584569140606909649984921079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-4999405950461777681775865627914600000000000000)
      constant := (136448129572810118127316139350101628600575924264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree090.table
  base := (6162314999593783557357831045329783432237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1140025271189713579333968592200000000000000)
      constant := (31335581556179444737197580389601659209494752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93020308415838838143/20000000000000000000)
  centralHi := (116275385519798547679/25000000000000000000)
  directionLo := (467707173346742673197/100000000000000000000)
  directionHi := (233853586673371336599/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree091.table
  base := (5090598471474360650287770504992874388229/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-5053424573946906844785220674389100000000000000)
      constant := (139433746822969532240228012967183028535663486640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree091.table
  base := (50731928625714159435848032884286814905643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1152345833061138561936864728700000000000000)
      constant := (32021390698466843303458731389123941778867716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467707173346742673197/100000000000000000000)
  centralHi := (233853586673371336599/50000000000000000000)
  directionLo := (470298368650748729721/100000000000000000000)
  directionHi := (235149184325374364861/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree092.table
  base := (26171725934353877883752067757062519696187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-5107443197432036007794575720863600000000000000)
      constant := (142451022361174330366087638871206553088426099984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree092.table
  base := (52172595931686473366882768821907547450447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1164666394932563544539760865200000000000000)
      constant := (32714473939303340851686830685262890569405364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470298368650748729721/100000000000000000000)
  centralHi := (235149184325374364861/50000000000000000000)
  directionLo := (118218841325925895933/25000000000000000000)
  directionHi := (472875365303703583733/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree093.table
  base := (53788004768044972614981664910337885208231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-5161461820917165170803930767338100000000000000)
      constant := (145499944976702448801293022080667179572199574696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree093.table
  base := (53620309960158610323998469717070255320429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1176986956803988527142657001700000000000000)
      constant := (33414828735234834182746257640517343063845148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118218841325925895933/25000000000000000000)
  centralHi := (472875365303703583733/100000000000000000000)
  directionLo := (475438394186530403171/100000000000000000000)
  directionHi := (118859598546632600793/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree094.table
  base := (55239438074149780023394961354247411693811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11280000000000000000000000000000000000000000
      center := (24161)
      previous := (0)
      next := (17575)
      square := (992685270783384312576202998000000000000000)
      linear := (-110967669029836049655601825825800000000000000)
      constant := (3161287314538774033532985092774166080390618808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree094.table
  base := (5507486493854570652897889653594900998499/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1189307518675413509745553138200000000000000)
      constant := (34122452616990304931298417386481388119819880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475438394186530403171/100000000000000000000)
  centralHi := (118859598546632600793/25000000000000000000)
  directionLo := (477987679989999556287/100000000000000000000)
  directionHi := (7468557499843743067/1562500000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree095.table
  base := (1771798512246024595058897124683006886013/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-5269499067887423496822640860287100000000000000)
      constant := (151692688209900882579708713167924873628203686656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree095.table
  base := (56536061095882553248115836171479525582011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1201628080546838492348449274700000000000000)
      constant := (34837343187318170592538811365870254306984132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477987679989999556287/100000000000000000000)
  centralHi := (7468557499843743067/1562500000000000000)
  directionLo := (480523441444616495389/100000000000000000000)
  directionHi := (48052344144461649539/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree096.table
  base := (58162154097489043790327579308523481344959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-5323517691372552659831995906761600000000000000)
      constant := (154836487991282555869423645278118280886984346344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree096.table
  base := (29001852243889173150955369962901303701467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1213948642418263474951345411200000000000000)
      constant := (35559498118885741516313456994309631288835208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480523441444616495389/100000000000000000000)
  centralHi := (48052344144461649539/10000000000000000000)
  directionLo := (483045891539647952457/100000000000000000000)
  directionHi := (241522945769823976229/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree097.table
  base := (29816527585822910069517596033355112548099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-5377536314857681822841350953236100000000000000)
      constant := (158011893159433395104639536364926565543700033168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree097.table
  base := (59477606826476881557836682901067478030651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1226269204289688457554241547700000000000000)
      constant := (36288915152239943253032031173025309736367812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell216.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483045891539647952457/100000000000000000000)
  centralHi := (241522945769823976229/50000000000000000000)
  directionLo := (485555237731907170587/100000000000000000000)
  directionHi := (121388809432976792647/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree098.table
  base := (30555036518572838353555654785215902043237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1135567)
      previous := (0)
      next := (826025)
      square := (46656207726819062691081540906000000000000000)
      linear := (-5431554938342810985850705999710600000000000000)
      constant := (161218894034840700839138791543781437525448505584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree098.table
  base := (7619698164484160731379083841220962127841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (259)
      previous := (0)
      next := (185)
      square := (10560481604078556516768117000000000000000)
      linear := (-1238589766161113440157137684200000000000000)
      constant := (37025592093827517324716201969607212364272736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell216.Kernel098
