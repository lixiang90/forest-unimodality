import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell079.Parameters
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch000_049
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch050_099
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch100_149
import ForestUnimodality.BinomialMassData.Q3493_6868.Batch150_199
import ForestUnimodality.BinomialMassData.Q26_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q26_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q26_51.Batch100_149
import ForestUnimodality.BinomialMassData.Q26_51.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree000.table
  base := (47457124339420450429694043/625000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (175472154788271043901470847500000000000)
      linear := (-3944512370664189941302235750000000000)
      constant := (189828497357681801718776172000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree000.table
  base := (47457124339420450429694043/625000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (175472154788271043901470847500000000000)
      linear := (-3944512370664189941302235750000000000)
      constant := (189828497357681801718776172000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree001.table
  base := (419660991879770700602633089140205791673907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-2151296922864705301537929627430222000000000000)
      constant := (1237756847117515468313450081650033054795136813723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree001.table
  base := (418852952461365332090401149019598142673713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-1902447324698369465856111211023000000000000)
      constant := (1089931927752172716533291632830032769094327513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49990387388164557157/100000000000000000000)
  directionHi := (24995193694082278579/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree002.table
  base := (244627761105581872949387463280553037912393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-4256078751608134518836404187300517000000000000)
      constant := (723372670244695684746516436766057643986108766977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree002.table
  base := (243797991481724333485217261867349903987709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-3763855942692348699562913961303000000000000)
      constant := (636058326057382936732785740920373100272031109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49990387388164557157/100000000000000000000)
  centralHi := (24995193694082278579/50000000000000000000)
  directionLo := (70697083832627241041/100000000000000000000)
  directionHi := (35348541916313620521/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree003.table
  base := (152298383967855046089811180822554422184023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-6360860580351563736134878747170812000000000000)
      constant := (453877286714493164453352151292930893067074182047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree003.table
  base := (151645504775669074874737224646303644719817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-625029395631814214807746301287000000000000)
      constant := (44307001484587181829324857447227753324027113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70697083832627241041/100000000000000000000)
  centralHi := (35348541916313620521/50000000000000000000)
  directionLo := (10823236355793929969/12500000000000000000)
  directionHi := (86585890846351439753/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree004.table
  base := (50922213350486676898263558843185877219981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-4232821204547496476716676653520553500000000000)
      constant := (154452420027632122947277613439623356087576566309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree004.table
  base := (101372872248953954490439327301474975828953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-7486673178680307166976519461863000000000000)
      constant := (271346154798745005526780593291048412131106753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10823236355793929969/12500000000000000000)
  centralHi := (86585890846351439753/100000000000000000000)
  directionLo := (49990387388164557157/50000000000000000000)
  directionHi := (19996154955265822863/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree005.table
  base := (72873443125982291368802101694448140625079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-10570424237838422170731827866911402000000000000)
      constant := (228336584003741122261445906693243575072248524031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree005.table
  base := (72539319620156068958551764626414483779981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-9348081796674286400683322212143000000000000)
      constant := (200641296463783072246175904376394072311730581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49990387388164557157/50000000000000000000)
  centralHi := (19996154955265822863/20000000000000000000)
  directionLo := (111781904421484115601/100000000000000000000)
  directionHi := (55890952210742057801/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree006.table
  base := (55136869909458068045644229066497716920337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-12675206066581851388030302426781697000000000000)
      constant := (181958841730853783673242330111202309777959385993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree006.table
  base := (13723978036711070363243239312364520230401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-311374733740785156510836804511750000000000)
      constant := (4444193308092651381594984509316346346585889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111781904421484115601/100000000000000000000)
  centralHi := (55890952210742057801/50000000000000000000)
  directionLo := (122450941145066631487/100000000000000000000)
  directionHi := (1913295955391666117/1562500000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree007.table
  base := (43460267469728942964849105364242731720421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-14779987895325280605328776986651992000000000000)
      constant := (154516904824711169283229206137975097839924225469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree007.table
  base := (5409947786828063301463616908291113158439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-3267724758165561217024231928175750000000000)
      constant := (33991501006110780363441222861751870650199678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122450941145066631487/100000000000000000000)
  centralHi := (1913295955391666117/1562500000000000000)
  directionLo := (132262132972863151623/100000000000000000000)
  directionHi := (16532766621607893953/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree008.table
  base := (17599297299170638971872496683613856918107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-8442384862034354911313625773261143500000000000)
      constant := (69106478197062200677545997831523294827845147523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree008.table
  base := (17528276274126054557289330371696469015731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-7466153825328112050901865231491500000000000)
      constant := (60857987972977396244010686022934515909916331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132262132972863151623/100000000000000000000)
  centralHi := (16532766621607893953/12500000000000000000)
  directionLo := (141394167665254482083/100000000000000000000)
  directionHi := (35348541916313620521/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree009.table
  base := (5794971496487796052285253856907844303819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-18989551552812139039925726106392582000000000000)
      constant := (128987496126344374355348759150286567654007259455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree009.table
  base := (28858126544692081402184847466240614990607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-1865968474294467037278948134807000000000000)
      constant := (12631210623957378513066282520921537732285423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141394167665254482083/100000000000000000000)
  centralHi := (35348541916313620521/25000000000000000000)
  directionLo := (149971162164493671471/100000000000000000000)
  directionHi := (9373197635280854467/6250000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree010.table
  base := (12026062196649042869952891877952000540591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-10547166690777784128612100333131438500000000000)
      constant := (62333991849084492727240769714658207821710380599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree010.table
  base := (23952777064039306512151593021691463344047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-18655124886644182569217335963543000000000000)
      constant := (109958060734454755143550681197599496157866247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149971162164493671471/100000000000000000000)
  centralHi := (9373197635280854467/6250000000000000000)
  directionLo := (9880217828797242221/6250000000000000000)
  directionHi := (158083485260755875537/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree011.table
  base := (4003990921567036391524175738955457646439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-23199115210298997474522675226133172000000000000)
      constant := (124044403328723980410018101384432466012163525355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree011.table
  base := (19933345144219216737637579691880632472107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-20516533504638161802924138713823000000000000)
      constant := (109488450842113887460389520189619525059950307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9880217828797242221/6250000000000000000)
  centralHi := (158083485260755875537/100000000000000000000)
  directionLo := (165799358091056499001/100000000000000000000)
  directionHi := (82899679045528249501/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree012.table
  base := (16637261651211697609788894001748120950203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-25303897039042426691821149786003467000000000000)
      constant := (126406010633488990382613037385822355143963012067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree012.table
  base := (8280322517140474605741921992377193367359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-1243219006812896724257274525783500000000000)
      constant := (6202774655576144958368477534529008883166751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165799358091056499001/100000000000000000000)
  centralHi := (82899679045528249501/50000000000000000000)
  directionLo := (34634356338540575901/20000000000000000000)
  directionHi := (86585890846351439753/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree013.table
  base := (6876547728871783311194729561680948863643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-13704339433892927954559812172936881000000000000)
      constant := (65653895692135771352086853614461330166968428227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree013.table
  base := (547391574390966143182451091638428252371/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-24239350740626120270337744214383000000000000)
      constant := (116052682548279559243190096000382797110424275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34634356338540575901/20000000000000000000)
  centralHi := (86585890846351439753/50000000000000000000)
  directionLo := (90121452504167821737/50000000000000000000)
  directionHi := (7209716200333425739/4000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree014.table
  base := (11266313907790291300643409107315067086481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-29513460696529285126418098905744057000000000000)
      constant := (138451569610722802166196297288661756811916684809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree014.table
  base := (1400651789332962878629819875711703777601/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-6525189839655024876011136741165750000000000)
      constant := (30608775156585843149471939108275283051080402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90121452504167821737/50000000000000000000)
  centralHi := (7209716200333425739/4000000000000000000)
  directionLo := (187046902238616793951/100000000000000000000)
  directionHi := (5845215694956774811/3125000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree015.table
  base := (9104730085967833489211594444316152988791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-31618242525272714343716573465614352000000000000)
      constant := (147624531861655155107345169627342046273571870399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree015.table
  base := (4525021105513048199364690965347597230013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-1553453776478559929875074984163500000000000)
      constant := (7256124676015167933026666216500455599473757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187046902238616793951/100000000000000000000)
  centralHi := (5845215694956774811/3125000000000000000)
  directionLo := (96805968912409308909/50000000000000000000)
  directionHi := (193611937824818617819/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree016.table
  base := (7214067695793644966303719707584742492943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-33723024354016143561015048025484647000000000000)
      constant := (158666666784447662422990793990521887911277835927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree016.table
  base := (7165161966168142236078909770000872786729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-29823576594608057971458152465223000000000000)
      constant := (140437370247983518864871673186300270118282129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96805968912409308909/50000000000000000000)
  centralHi := (193611937824818617819/100000000000000000000)
  directionLo := (49990387388164557157/25000000000000000000)
  directionHi := (199961549552658228629/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree017.table
  base := (346993820236392116356266284744243755359/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (387638)
      previous := (193819)
      next := (193819)
      square := (1789991450995152918838904115347500000000000)
      linear := (-30992911922802398597157026457919500000000000)
      constant := (148315657348326653801478860798130778443668636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree017.table
  base := (2754119567557251449733282321405579871443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (684)
      previous := (342)
      next := (342)
      square := (3158498786188878790226475255000000000000)
      linear := (-54818313516612521116202344663500000000000)
      constant := (262640773311581328033231275489650218842987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49990387388164557157/25000000000000000000)
  centralHi := (199961549552658228629/100000000000000000000)
  directionLo := (1030578237334737171/500000000000000000)
  directionHi := (206115647466947434201/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree018.table
  base := (4084165832125395351565432976764719374377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-37932588011503001995611997145225237000000000000)
      constant := (185882805903106196700324264250005175775687715553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree018.table
  base := (809052815768064156008211441372143356919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-3727377092288446270985750885087000000000000)
      constant := (18292086141722314929873977828658747150747955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1030578237334737171/500000000000000000)
  centralHi := (206115647466947434201/100000000000000000000)
  directionLo := (53022812874470430781/25000000000000000000)
  directionHi := (339346002396610757/160000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree019.table
  base := (173939017550645428054390810628372433619/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-10009342460061607803227617926273883000000000000)
      constant := (50468579316067741936280801770186351719071616364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree019.table
  base := (274843749700641113029775910678965357311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-17703901224294997836289280358031500000000000)
      constant := (89416144586010889816793252254370944471829555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53022812874470430781/25000000000000000000)
  centralHi := (339346002396610757/160000000000000000)
  directionLo := (217903046773459499229/100000000000000000000)
  directionHi := (21790304677345949923/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree020.table
  base := (1625470906817810025618389331068795780467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-42142151668989860430208946264965827000000000000)
      constant := (219359611530884042663982015509906940083641177563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree020.table
  base := (1594785084059922124059535768387018055719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-37269211066583974906285363466343000000000000)
      constant := (194357152494913875797483062357934633962925119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217903046773459499229/100000000000000000000)
  centralHi := (21790304677345949923/10000000000000000000)
  directionLo := (223563808842968231203/100000000000000000000)
  directionHi := (55890952210742057801/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree021.table
  base := (592359036443781333688830313419177255919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-44246933497733289647507420824836122000000000000)
      constant := (238282242604811882455384164139086471482224988791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree021.table
  base := (565188861452630040077380850476111914793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-4347846631619772682221351801847000000000000)
      constant := (23461515486885910329065200945789596343375177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223563808842968231203/100000000000000000000)
  centralHi := (55890952210742057801/25000000000000000000)
  directionLo := (229084734226429855111/100000000000000000000)
  directionHi := (28635591778303731889/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree022.table
  base := (-10384902659243373274511532605646845983/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-11587928831619179716201473846176604250000000000)
      constant := (64648756171514198670126239288917593063782588104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree022.table
  base := (-356328845050184360032032625423491818327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-40992028302571933373698968966903000000000000)
      constant := (229180191902515226386862709500229497780531473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229084734226429855111/100000000000000000000)
  centralHi := (28635591778303731889/12500000000000000000)
  directionLo := (117237850422562725697/50000000000000000000)
  directionHi := (46895140169025090279/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree023.table
  base := (-14524676005279147450353060876883051849/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-12114124288805037020526092486144178000000000000)
      constant := (70064600652049494660080579459946549192400668780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree023.table
  base := (-1183157726117316581591575751442222152727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-42853436920565912607405771717183000000000000)
      constant := (248401983471110438963965977611672780180757073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117237850422562725697/50000000000000000000)
  centralHi := (46895140169025090279/20000000000000000000)
  directionLo := (239745475698774191353/100000000000000000000)
  directionHi := (119872737849387095677/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree024.table
  base := (-14905315754912072264924307805241942831/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-12640319745990894324850711126111751750000000000)
      constant := (75809789424051352129782289006549931252041601312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree024.table
  base := (-1926538555771131694279498019043703851717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-4968316170951099093456952718607000000000000)
      constant := (29865530759391851016295942879904369586853787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239745475698774191353/100000000000000000000)
  centralHi := (119872737849387095677/50000000000000000000)
  directionLo := (122450941145066631487/50000000000000000000)
  directionHi := (9796075291605330519/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree025.table
  base := (-2579510237792614793515621143647554357571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-52666060812707006516701319064317302000000000000)
      constant := (327509358740521736447801386335421915746542868181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree025.table
  base := (-2595919307080905178772271950918677435357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-46576254156553871074819377217743000000000000)
      constant := (290318997814810701409715729391110519990636443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122450941145066631487/50000000000000000000)
  centralHi := (9796075291605330519/4000000000000000000)
  directionLo := (49990387388164557157/20000000000000000000)
  directionHi := (124975968470411392893/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree026.table
  base := (-127393466220539906563096258543527976583/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-54770842641450435733999793624187597000000000000)
      constant := (353045500298544535330381326013354165776085002825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree026.table
  base := (-1599623873864732284706636062228285657813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-24218831387273925154263089984011500000000000)
      constant := (156484487134109765668147795375898229004028387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49990387388164557157/20000000000000000000)
  centralHi := (124975968470411392893/50000000000000000000)
  directionLo := (25490196078431372549/10000000000000000000)
  directionHi := (254901960784313725491/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree027.table
  base := (-3730573675224924236792002488503359752717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-56875624470193864951298268184057892000000000000)
      constant := (379827788884709274036586786624078315774972292187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree027.table
  base := (-3743213821457210073158584520489177472197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-5588785710282425504692553635367000000000000)
      constant := (37413589516787151998678921151672627710535067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25490196078431372549/10000000000000000000)
  centralHi := (254901960784313725491/100000000000000000000)
  directionLo := (259757672539054319257/100000000000000000000)
  directionHi := (129878836269527159629/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree028.table
  base := (-4222377838868398998411471567460846054387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-58980406298937294168596742743928187000000000000)
      constant := (407839548509940164545573367428993392816368283557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree028.table
  base := (-2116725736734733430624270157538225499979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-26080240005267904387969892734291500000000000)
      constant := (180782169035963080297381863420975075474554621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259757672539054319257/100000000000000000000)
  centralHi := (129878836269527159629/50000000000000000000)
  directionLo := (132262132972863151623/50000000000000000000)
  directionHi := (264524265945726303247/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree029.table
  base := (-4665016724968109415262120881529988897533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-61085188127680723385895217303798482000000000000)
      constant := (437066723928433413553926611816967895186060835563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree029.table
  base := (-4674707261244339723389762339061314426373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-54021888628529788009646588218863000000000000)
      constant := (387482725734744358598228974199463521177003827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132262132972863151623/50000000000000000000)
  centralHi := (264524265945726303247/100000000000000000000)
  directionLo := (134603237428882165077/50000000000000000000)
  directionHi := (53841294971552866031/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree030.table
  base := (-5062510066723829018072699711473482564919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-63189969956424152603193691863668777000000000000)
      constant := (467497464608959833913213932049627412258670510209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree030.table
  base := (-1014196304232784544967630636992314022207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-6209255249613751915928154552127000000000000)
      constant := (46051895973845459481641714421606106237910885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134603237428882165077/50000000000000000000)
  centralHi := (53841294971552866031/20000000000000000000)
  directionLo := (273808628309194924899/100000000000000000000)
  directionHi := (2738086283091949249/1000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree031.table
  base := (-5418248115655472876980339107207712265859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-65294751785167581820492166423539072000000000000)
      constant := (499121775788306330724229823587154997878856006549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree031.table
  base := (-678205841383808472430968806396374573009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-14436176466129436619265048429855750000000000)
      constant := (110627145086663198394117185458375559471207182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273808628309194924899/100000000000000000000)
  centralHi := (2738086283091949249/1000000000000000000)
  directionLo := (139167348691944999679/50000000000000000000)
  directionHi := (278334697383889999359/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree032.table
  base := (-5735091025711018791324229027587559612149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-67399533613911011037790640983409367000000000000)
      constant := (531931225478080564064498213242940122970579266739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree032.table
  base := (-5741546855923733676030443093143165148999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-59606114482511725710766996469703000000000000)
      constant := (471599878328015000713609187143470627447453601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139167348691944999679/50000000000000000000)
  centralHi := (278334697383889999359/100000000000000000000)
  directionLo := (141394167665254482083/50000000000000000000)
  directionHi := (282788335330508964167/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree033.table
  base := (-6015452367775828374791162600819138778307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-69504315442654440255089115543279662000000000000)
      constant := (565918698256504679099686816750442752603199694677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree033.table
  base := (-1505270199303274181119743901577055548361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-1707431197236269581790938867221750000000000)
      constant := (13937075504608941360115714924770730946523671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141394167665254482083/50000000000000000000)
  centralHi := (282788335330508964167/100000000000000000000)
  directionLo := (287172912076015878677/100000000000000000000)
  directionHi := (143586456038007939339/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree034.table
  base := (-1565342338221706151588652838883972119419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25502500000000000000000000000000000000000000
      center := (387638)
      previous := (193819)
      next := (193819)
      square := (1789991450995152918838904115347500000000000)
      linear := (-61945585874911651792722828808953250000000000)
      constant := (519963830661012149309374317823776350409806781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree034.table
  base := (-3133136266620649293263542243024010956319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (684)
      previous := (342)
      next := (342)
      square := (3158498786188878790226475255000000000000)
      linear := (-109565625810553086813461249083500000000000)
      constant := (921985874555031189041468760646783901393129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287172912076015878677/100000000000000000000)
  centralHi := (143586456038007939339/50000000000000000000)
  directionLo := (291491544065068735737/100000000000000000000)
  directionHi := (145745772032534367869/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree035.table
  base := (-6474561910394585476766563337043862084677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-73713879100141298689686064663020252000000000000)
      constant := (637404624936157444452169859519969970795646667747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree035.table
  base := (-323941505174544328708420536734019522851/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-16297585084123415852971851180135750000000000)
      constant := (141278696924494827515130836495681576105322745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291491544065068735737/100000000000000000000)
  centralHi := (145745772032534367869/50000000000000000000)
  directionLo := (36968390022054794329/12500000000000000000)
  directionHi := (295747120176438354633/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree036.table
  base := (-6656482412439338590342909459305441237399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-75818660928884727906984539222890547000000000000)
      constant := (674893726610256367193506230568843838047877619489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree036.table
  base := (-832524404223024748138318915956326638639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-1862548582069101184599839096411750000000000)
      constant := (16620884023682551056569496904035243202866658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36968390022054794329/12500000000000000000)
  centralHi := (295747120176438354633/100000000000000000000)
  directionLo := (149971162164493671471/50000000000000000000)
  directionHi := (299942324328987342943/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree037.table
  base := (-1702089385659156993097175159964088050899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-19480860689407039281070753445690210500000000000)
      constant := (178385469223488336813907070574120020278363217989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree037.table
  base := (-3405792552061532564255816796401666117159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-34456578786240810939650505110551500000000000)
      constant := (316307890535700422678876535080872266429269441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149971162164493671471/50000000000000000000)
  centralHi := (299942324328987342943/100000000000000000000)
  directionLo := (304079655279820051529/100000000000000000000)
  directionHi := (30407965527982005153/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree038.table
  base := (-866402945388775488784208651077073973693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-20007056146592896585395372085657784250000000000)
      constant := (188336505198570059944398616972024296631938754646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree038.table
  base := (-6934027516242157722183477826769945917323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-70774566190475601113007812971383000000000000)
      constant := (667903983042154456088279558240615370669042877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304079655279820051529/100000000000000000000)
  centralHi := (30407965527982005153/10000000000000000000)
  directionLo := (308161444029445313337/100000000000000000000)
  directionHi := (154080722014722656669/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree039.table
  base := (-7025956030953366000393194397920286905091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-82133006415115015558879962902501432000000000000)
      constant := (794303577091001416245567130178022470423257178901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree039.table
  base := (-7028390513989661538452170905523512009589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-8070663867607731149634957302407000000000000)
      constant := (78246019220309282114916755201941705029228779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308161444029445313337/100000000000000000000)
  centralHi := (154080722014722656669/50000000000000000000)
  directionLo := (62437973835649637797/20000000000000000000)
  directionHi := (156094934589124094493/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree040.table
  base := (-1418658969142453405686965536486337138939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-84237788243858444776178437462371727000000000000)
      constant := (836412364494403758639741441226864484152012312145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree040.table
  base := (-886925917436382103556428941496081472979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-18624345856615889895105354617985750000000000)
      constant := (185386110932629930015616995886517384177563242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62437973835649637797/20000000000000000000)
  centralHi := (156094934589124094493/50000000000000000000)
  directionLo := (316166970521511751073/100000000000000000000)
  directionHi := (158083485260755875537/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree041.table
  base := (-3566932683906868056933030565185677458011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-43171285036300936996738456011121011000000000000)
      constant := (439835269693145948364067800905357462640989809021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree041.table
  base := (-3567848732934448447767271186633169787211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-38179396022228769407064110611111500000000000)
      constant := (389946592017885619015454615104556125383464189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316166970521511751073/100000000000000000000)
  centralHi := (158083485260755875537/50000000000000000000)
  directionLo := (64018932224762775279/20000000000000000000)
  directionHi := (80023665280953469099/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree042.table
  base := (-3574098114656108131275210449043884947187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-44223675950672651605387693291056158500000000000)
      constant := (462038271656160539842018207483415286769932424357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree042.table
  base := (-7149784328358522319668361466509347985929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-8691133406939057560870558219167000000000000)
      constant := (91028781382610108010120082116902798432066519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64018932224762775279/20000000000000000000)
  centralHi := (80023665280953469099/25000000000000000000)
  directionLo := (64794947615130612007/20000000000000000000)
  directionHi := (80993684518913265009/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree043.table
  base := (-7136734359045217707937458667377818495419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-90552133730088732428073861141982612000000000000)
      constant := (969629058686501660800823825327174523574658695709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree043.table
  base := (-7138110276089803547583936175276304125393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-80081609280445497281541826722783000000000000)
      constant := (859640838403592129211035055882440332969852807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64794947615130612007/20000000000000000000)
  centralHi := (80993684518913265009/25000000000000000000)
  directionLo := (65561778420786227671/20000000000000000000)
  directionHi := (81952223025982784589/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree044.table
  base := (-1774964415268370504363841452345823074407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-23164228889708040411343083925463226750000000000)
      constant := (254081742853507278132930005905147185548394541777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree044.table
  base := (-3550524591692818688362920445204123091299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-40971508949219738257624314736531500000000000)
      constant := (450518814734480427410309421354740075839531301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65561778420786227671/20000000000000000000)
  centralHi := (81952223025982784589/25000000000000000000)
  directionLo := (331598716182112998003/100000000000000000000)
  directionHi := (82899679045528249501/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree045.table
  base := (-3518942857747245360149061367577217611713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-47380848693787795431335405130861601000000000000)
      constant := (532084669672166715326402528665520263420802633543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree045.table
  base := (-7038917089495001771142440517453363876081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-9311602946270383972106159135927000000000000)
      constant := (104827620402390061915038033601545977839812591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331598716182112998003/100000000000000000000)
  centralHi := (82899679045528249501/25000000000000000000)
  directionLo := (83836428316113086701/25000000000000000000)
  directionHi := (67069142652890469361/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree046.table
  base := (-3475544406078063732838557719538656977313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-48433239608159510039984642410796748500000000000)
      constant := (556577682819443628852279490366863126290410295143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree046.table
  base := (-3475990588508925081957185064092754547157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-42832917567213717491331117486811500000000000)
      constant := (493436502959649378787881351587028745422844643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83836428316113086701/25000000000000000000)
  centralHi := (67069142652890469361/20000000000000000000)
  directionLo := (10595353226587366817/3125000000000000000)
  directionHi := (67810260650159147629/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree047.table
  base := (-6839695578629346823274014736051416065437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-98971261045062449297267759381463792000000000000)
      constant := (1163284376283263565800603526597619703988061900107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree047.table
  base := (-6840467350047927713738883232584392517749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-87527243752421414216369037723903000000000000)
      constant := (1031310308785777624684108488610453995061334851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10595353226587366817/3125000000000000000)
  centralHi := (67810260650159147629/20000000000000000000)
  directionLo := (85679207318375170749/25000000000000000000)
  directionHi := (342716829273500682997/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree048.table
  base := (-6703899422497253415819017044810907555367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-101076042873805878514566233941334087000000000000)
      constant := (1214555801094694087616818652892811292356005656337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree048.table
  base := (-1340913326344307343997557369488496733623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-9932072485601710383341760052687000000000000)
      constant := (119639999485529959586634843185825122219914765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85679207318375170749/25000000000000000000)
  centralHi := (342716829273500682997/100000000000000000000)
  directionLo := (34634356338540575901/10000000000000000000)
  directionHi := (346343563385405759011/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree049.table
  base := (-817982996663531799795041877843786987119/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-25795206175637326932966177125301095500000000000)
      constant := (316742289419676772262971357353593875386112668818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree049.table
  base := (-409027535383354431264280792386877876717/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-22812515247102343170945660806115750000000000)
      constant := (280805411373770928425796291378537422570636332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34634356338540575901/10000000000000000000)
  centralHi := (346343563385405759011/100000000000000000000)
  directionLo := (349932711717151900099/100000000000000000000)
  directionHi := (3499327117171519001/1000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree050.table
  base := (-6359727680357980733132388849705419378609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-105285606531292736949163183061074677000000000000)
      constant := (1320524037874457062717981146608760274889535971799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree050.table
  base := (-3180112890198739676620799232263755758707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-46555734803201675958744722987371500000000000)
      constant := (585347451897299278074297442207331971271603093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349932711717151900099/100000000000000000000)
  centralHi := (3499327117171519001/1000000000000000000)
  directionLo := (353485419163136205207/100000000000000000000)
  directionHi := (44185677395392025651/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree051.table
  base := (-3075803848959081833738717244455962385047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (775276)
      previous := (387638)
      next := (387638)
      square := (3579982901990305837677808230695000000000000)
      linear := (-185796519654041809976577262319974000000000000)
      constant := (2379273523011633589470345710096135290210135553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree051.table
  base := (-1230407567616850326864486554579369635019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (152)
      previous := (76)
      next := (76)
      square := (701888619153084175605883390000000000000)
      linear := (-36513986245443033891271145223000000000000)
      constant := (468734897995949726829150171385103151824905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353485419163136205207/100000000000000000000)
  centralHi := (44185677395392025651/12500000000000000000)
  directionLo := (357002773647708320917/100000000000000000000)
  directionHi := (178501386823854160459/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree052.table
  base := (-73995039610946859309297518658568096333/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-27373792547194898845940033045203816750000000000)
      constant := (357764260168863528159894304343309155038994847260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree052.table
  base := (-2959987247320500681763768128373011086837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-48417143421195655192451525737651500000000000)
      constant := (634337544455883040639746118674249798163136963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357002773647708320917/100000000000000000000)
  centralHi := (178501386823854160459/50000000000000000000)
  directionLo := (360485810016671286949/100000000000000000000)
  directionHi := (7209716200333425739/2000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree053.table
  base := (-113275960007173267374511723840632765979/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-55799976008761512300529303370342781000000000000)
      constant := (744017311816482946061604701881696713051943396725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree053.table
  base := (-1416029612003819699996603014862887094423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-24673923865096322404652463556395750000000000)
      constant := (329795386592534875828804242866570130667405777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360485810016671286949/100000000000000000000)
  centralHi := (7209716200333425739/2000000000000000000)
  directionLo := (9098387839838522279/2500000000000000000)
  directionHi := (363935513593540891161/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree054.table
  base := (-5384263210283473333135417995513460919337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-113704733846266453818357081300555857000000000000)
      constant := (1546152635806120922630535907685575634511772703007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree054.table
  base := (-2692269831548942720113003720690879736407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-5586505782132181602906480943103500000000000)
      constant := (76149925560216918383184844905654335756178377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9098387839838522279/2500000000000000000)
  centralHi := (363935513593540891161/100000000000000000000)
  directionLo := (367352823435199894461/100000000000000000000)
  directionHi := (183676411717599947231/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree055.table
  base := (-5081058911426847514448115540551149964623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-115809515675009883035655555860426152000000000000)
      constant := (1605410899977103547190178957537809663976944544553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree055.table
  base := (-5081297336284514935032553937275404147621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-102418512696373248086023459726143000000000000)
      constant := (1423226276083235964840127959633136673812037779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367352823435199894461/100000000000000000000)
  centralHi := (183676411717599947231/50000000000000000000)
  directionLo := (9268465882935802459/2500000000000000000)
  directionHi := (370738635317432098361/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree056.table
  base := (-4754235989230124309489166868327289027319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-117914297503753312252954030420296447000000000000)
      constant := (1665809266131103895929179697106253592818740156609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree056.table
  base := (-4754441556088833250204301607922836670117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-104279921314367227319730262476423000000000000)
      constant := (1476764264087909759966577977052240701821025683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9268465882935802459/2500000000000000000)
  centralHi := (370738635317432098361/100000000000000000000)
  directionLo := (187046902238616793951/50000000000000000000)
  directionHi := (374093804477233587903/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree057.table
  base := (-4403837520786249090128047490464263789957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-120019079332496741470252504980166742000000000000)
      constant := (1727347607273018104619128816199324093652729457827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree057.table
  base := (-110100367675083268618848649405331130347/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-2948370275898922404262140700741750000000000)
      constant := (42536458718218359690357923319557093033297170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187046902238616793951/50000000000000000000)
  centralHi := (374093804477233587903/100000000000000000000)
  directionLo := (377419148135689367321/100000000000000000000)
  directionHi := (188709574067844683661/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree058.table
  base := (-4029899975072285593028549613681562380359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-122123861161240170687550979540037037000000000000)
      constant := (1790025815889056050405668892314105717443649816049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree058.table
  base := (-4030052656441285144193183126410819724051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-108002738550355185787143867976983000000000000)
      constant := (1586870932095947596134993825473409457897743349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377419148135689367321/100000000000000000000)
  centralHi := (188709574067844683661/50000000000000000000)
  directionLo := (380715447822501939579/100000000000000000000)
  directionHi := (19035772391125096979/5000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree059.table
  base := (-181622711413067880711039690223418377699/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-31057160747495899976212363524976833000000000000)
      constant := (463460950238377846232521320834964483972788663945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree059.table
  base := (-3632585758385792743788042398125263375719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-109864147168349165020850670727263000000000000)
      constant := (1643439439857459668348916792647978189959754881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380715447822501939579/100000000000000000000)
  centralHi := (19035772391125096979/5000000000000000000)
  directionLo := (191991725760452342769/50000000000000000000)
  directionHi := (383983451520904685539/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree060.table
  base := (-321152642269270495387149525861794128327/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-63166712409363514561073964329888813500000000000)
      constant := (959400742698220680534572149020864893550072914485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree060.table
  base := (-1605819851068649202450534877916172182477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-6206975321463508014142081859863500000000000)
      constant := (94500998351251483800569453276342226239264147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191991725760452342769/50000000000000000000)
  centralHi := (383983451520904685539/100000000000000000000)
  directionLo := (96805968912409308909/25000000000000000000)
  directionHi := (387223875649637235637/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree061.table
  base := (-2767138693644078002552771801358092709509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-128438206647470458339446403219647922000000000000)
      constant := (1984898803961077130951654572152463244447116321699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree061.table
  base := (-2767236230135803796010473496424297736329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-113586964404337123488264276227823000000000000)
      constant := (1759606466939062271979282104671738401587808271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96805968912409308909/25000000000000000000)
  centralHi := (387223875649637235637/100000000000000000000)
  directionLo := (97609351724215083943/25000000000000000000)
  directionHi := (390437406896860335773/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree062.table
  base := (-459861956861576709279927484329300603039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-130542988476213887556744877779518217000000000000)
      constant := (2052135701390819335247886118416366046572436787645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree062.table
  base := (-1149696872554421958646656944438651634339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-57724186511165551360985539489051500000000000)
      constant := (909602440920786020260276047990553067099084261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97609351724215083943/25000000000000000000)
  centralHi := (390437406896860335773/100000000000000000000)
  directionLo := (384399124921199663/97656250000000000)
  directionHi := (393624703919308454913/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree063.table
  base := (-1808055566212739327891431220511011405663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-132647770304957316774043352339388512000000000000)
      constant := (2120512130894989042806030764502428132021090371993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree063.table
  base := (-226015977956600576048903038892696645259/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-3258605045564585609879941159121750000000000)
      constant := (52217032625425800401809784569061521339040298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384399124921199663/97656250000000000)
  centralHi := (393624703919308454913/100000000000000000000)
  directionLo := (396786398918589454869/100000000000000000000)
  directionHi := (39678639891858945487/10000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree064.table
  base := (-1293389479663996897516352586048879691963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-134752552133700745991341826899258807000000000000)
      constant := (2190028052850369890078961305164793232317800491293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree064.table
  base := (-80840728168865351293294296523175389711/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-29792797564579765297346171119665750000000000)
      constant := (485357827666579711074930262833020883245446756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396786398918589454869/100000000000000000000)
  centralHi := (39678639891858945487/10000000000000000000)
  directionLo := (399923099105316457257/100000000000000000000)
  directionHi := (199961549552658228629/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree065.table
  base := (-75532290652339315588851542442193945219/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-68428666981222087604320150729564551000000000000)
      constant := (1130341716851110245494541588975979309783666317545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree065.table
  base := (-755376387098697962830290661836126126719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-121032598876313040423091487228943000000000000)
      constant := (2004059261265190186670805322964734235944403881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399923099105316457257/100000000000000000000)
  centralHi := (199961549552658228629/50000000000000000000)
  directionLo := (80607077612135159443/20000000000000000000)
  directionHi := (12594855876896118663/3125000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree066.table
  base := (-193865485744469741273747521175088412101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-138962115791187604425938776018999397000000000000)
      constant := (2332478245034047937921582916893465021778257575011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree066.table
  base := (-96955740295088300077512242126480373743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-6827444860794834425377682776623500000000000)
      constant := (114872055652130743102973720379771447171988273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80607077612135159443/20000000000000000000)
  centralHi := (12594855876896118663/3125000000000000000)
  directionLo := (406123827004078022199/100000000000000000000)
  directionHi := (2030619135020390111/500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree067.table
  base := (390974619527859952264312737215940464859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-141066897619931033643237250578869692000000000000)
      constant := (2405412462780174506293468844362165581834105704451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree067.table
  base := (390935071027139496588043428873169987027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-124755416112300998890505092729503000000000000)
      constant := (2132344511283539509944978117364465115136257227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406123827004078022199/100000000000000000000)
  centralHi := (2030619135020390111/500000000000000000)
  directionLo := (51148619496836290313/12500000000000000000)
  directionHi := (81837791194938064501/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree068.table
  base := (999190495844245965847645009616945691119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1550552)
      previous := (775276)
      next := (775276)
      square := (7159965803980611675355616461390000000000000)
      linear := (-495403735116520632735417734044083000000000000)
      constant := (8579536562488360607037447115047011462995104919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree068.table
  base := (999156497234899766927763880329084668179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1368)
      previous := (684)
      next := (684)
      square := (6316997572377757580452950510000000000000)
      linear := (-438120500796868436415958115847000000000000)
      constant := (7605542464673461450302329811378961762013611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51148619496836290313/12500000000000000000)
  centralHi := (81837791194938064501/20000000000000000000)
  directionLo := (1030578237334737171/250000000000000000)
  directionHi := (412231294933894868401/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree069.table
  base := (101923518001474865512988772118550368849/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-36319115319354473019458549924652570500000000000)
      constant := (638674759777334524893813385285287204809648718244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree069.table
  base := (203843383294799791453249010366826756371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-3568839815230248815497741617501750000000000)
      constant := (62907465829209444817744837406016525865182438) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1030578237334737171/250000000000000000)
  centralHi := (412231294933894868401/100000000000000000000)
  directionLo := (103812836198761621099/25000000000000000000)
  directionHi := (415251344795046484397/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree070.table
  base := (18285816296653734532881516171854060031/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-147381243106161321295132674258480577000000000000)
      constant := (2631051365811253391112569409671274522997841344875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree070.table
  base := (2285701926096334916206376596574044652923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-130339641966282936591625500980343000000000000)
      constant := (2332345491345432790835387620652949090142252723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103812836198761621099/25000000000000000000)
  centralHi := (415251344795046484397/100000000000000000000)
  directionLo := (418249588386304740213/100000000000000000000)
  directionHi := (209124794193152370107/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree071.table
  base := (370504817875858948655645699529553045471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-37371506233726187628107787204587718000000000000)
      constant := (677135758570718426295727769639240199797789109838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree071.table
  base := (592803393711157877514724469864714510837/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-132201050584276915825332303730623000000000000)
      constant := (2401031926087679206060912875115508612213435185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418249588386304740213/100000000000000000000)
  centralHi := (209124794193152370107/50000000000000000000)
  directionLo := (10530662283794527061/2500000000000000000)
  directionHi := (421226491351781082441/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree072.table
  base := (3665707248567368501529285543116652403387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-151590806763648179729729623378221167000000000000)
      constant := (2787174034037163415242350350842687362667248777443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree072.table
  base := (458211089502652221906856852697740778173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-3723957200063080418306641846691750000000000)
      constant := (68631335139798364701338610093855294169783994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10530662283794527061/2500000000000000000)
  centralHi := (421226491351781082441/100000000000000000000)
  directionLo := (424182502995763446249/100000000000000000000)
  directionHi := (339346002396610757/80000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree073.table
  base := (4390730140923080338309746172093277128891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-153695588592391608947028097938091462000000000000)
      constant := (2866944356192001683489294614124764323902635139299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree073.table
  base := (4390714224267789735213256195967670147683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-135923867820264874292745909231183000000000000)
      constant := (2541433900522689776672379122299785910054123483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424182502995763446249/100000000000000000000)
  centralHi := (339346002396610757/80000000000000000)
  directionLo := (106779514268588062779/25000000000000000000)
  directionHi := (427118057074352251117/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree074.table
  base := (5139104668309279310885368853577309374833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-155800370421135038164326572497961757000000000000)
      constant := (2947853993224558985341879599398265309417542044137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree074.table
  base := (5139091000720996858549353705470125836449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-137785276438258853526452711981463000000000000)
      constant := (2613149426074338851961932823211499797300603849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106779514268588062779/25000000000000000000)
  centralHi := (427118057074352251117/100000000000000000000)
  directionLo := (215016786269228517809/50000000000000000000)
  directionHi := (430033572538457035619/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree075.table
  base := (295541433474049045442473115381704928893/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-39476288062469616845406261764458013000000000000)
      constant := (757475734690823188914951238643604763791826177385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree075.table
  base := (5910816935180114602206905770195777928761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-15516298339583648084462168303527000000000000)
      constant := (298430515133228474508929086862736579821411929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215016786269228517809/50000000000000000000)
  centralHi := (430033572538457035619/100000000000000000000)
  directionLo := (216464727115878599381/50000000000000000000)
  directionHi := (432929454231757198763/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree076.table
  base := (33529501569805906773972489536575370199/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-40002483519655474149730880404425586750000000000)
      constant := (778272796852948468713484273997733344077729985550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree076.table
  base := (1341178048234914276313892415128086343187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-141508093674246811993866317482023000000000000)
      constant := (2759609526250232075836078610691148762893146935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216464727115878599381/50000000000000000000)
  centralHi := (432929454231757198763/100000000000000000000)
  directionLo := (217903046773459499229/50000000000000000000)
  directionHi := (435806093546918998459/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree077.table
  base := (7524318051436858437123334486249088515013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-162114715907365325816221996177572642000000000000)
      constant := (3197418734599601575585510819343782323736136160157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree077.table
  base := (7524309406319507394709081841879435620257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-143369502292240791227573120232303000000000000)
      constant := (2834354092294153247384268736022474412048288457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217903046773459499229/50000000000000000000)
  centralHi := (435806093546918998459/100000000000000000000)
  directionLo := (109665967260770067013/25000000000000000000)
  directionHi := (438663869043080268053/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree078.table
  base := (2091520142225212233447898790754104081237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-41054874434027188758380117684360734250000000000)
      constant := (820721394113963470759603134909249524946749906093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree078.table
  base := (1673214630057637626563124868879747312677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-16136767878914974495697769220287000000000000)
      constant := (323345370111187772085279664637127234866818265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109665967260770067013/25000000000000000000)
  centralHi := (438663869043080268053/100000000000000000000)
  directionLo := (220751573513680439371/50000000000000000000)
  directionHi := (441503147027360878743/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree079.table
  base := (461559337717642594675946653007643395781/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-41581069891213046062704736324328308000000000000)
      constant := (842372927425568735495370782581236044836373062545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree079.table
  base := (9231180389231564165461931084126934691457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-147092319528228749694986725732863000000000000)
      constant := (2986872239550750802417282308570076157132479657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220751573513680439371/50000000000000000000)
  centralHi := (441503147027360878743/100000000000000000000)
  directionLo := (55540535262865979709/12500000000000000000)
  directionHi := (444324282102927837673/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree080.table
  base := (2529908916513716685439562410993108258211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-42107265348398903367029354964295881750000000000)
      constant := (864309282890634328009726652559636176531841008779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree080.table
  base := (632476887853445622810863683249663693551/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-37238432036555682232173382120785750000000000)
      constant := (766161453889483149864021041552889501067704604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55540535262865979709/12500000000000000000)
  centralHi := (444324282102927837673/100000000000000000000)
  directionLo := (223563808842968231203/50000000000000000000)
  directionHi := (447127617685936462407/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree081.table
  base := (11031426506490456319374819353508571407811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-170533843222339042685415894417053822000000000000)
      constant := (3546121839685491557502646645433495393398082123179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree081.table
  base := (5515710911457695776648868548501689733587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-8378618709123150453466685068523500000000000)
      constant := (174634947611232534002611403836177988333006643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223563808842968231203/50000000000000000000)
  centralHi := (447127617685936462407/100000000000000000000)
  directionLo := (224956743246740507207/50000000000000000000)
  directionHi := (89982697298696202883/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree082.table
  base := (11966558600307637140335684814056540889887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-172638625051082471902714368976924117000000000000)
      constant := (3636145832080139924729347820635960312575526075943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree082.table
  base := (11966554583626982625229196033906974613493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-152676545382210687396107133983703000000000000)
      constant := (3223221962173650502430208739781828040969695293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224956743246740507207/50000000000000000000)
  centralHi := (89982697298696202883/20000000000000000000)
  directionLo := (3621457688036139827/800000000000000000)
  directionHi := (56585276375564684797/12500000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree083.table
  base := (12925031375635586146658825333892695702671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-174743406879825901120012843536794412000000000000)
      constant := (3727309107060556330840826978446896592506391645719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree083.table
  base := (12925027931380386270096968411791540780577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-154537954000204666629813936733983000000000000)
      constant := (3304024529625106117121038716115723797570280777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3621457688036139827/800000000000000000)
  centralHi := (56585276375564684797/12500000000000000000)
  directionLo := (45543410389556604571/10000000000000000000)
  directionHi := (455434103895566045711/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree084.table
  base := (1738355543532349533830240942929277658049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-44212047177142332584327829524166176750000000000)
      constant := (954902915799807591455342168386721050733280036722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree084.table
  base := (13906841395262379909454696778650048281111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-17377706957577627318168971053807000000000000)
      constant := (376204084236856351576995135813357863953241079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45543410389556604571/10000000000000000000)
  centralHi := (455434103895566045711/100000000000000000000)
  directionLo := (229084734226429855111/50000000000000000000)
  directionHi := (458169468452859710223/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree085.table
  base := (14911997108211418035390026610964718969583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1550552)
      previous := (775276)
      next := (775276)
      square := (7159965803980611675355616461390000000000000)
      linear := (-619214430924957645517680943448218000000000000)
      constant := (13539977506185281032707553999862121723208716183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree085.table
  base := (14911994576749307565625095324620680847707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1368)
      previous := (684)
      next := (684)
      square := (6316997572377757580452950510000000000000)
      linear := (-547615125384749567810475924687000000000000)
      constant := (12002279054176102472138486636691586127629363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229084734226429855111/50000000000000000000)
  centralHi := (458169468452859710223/100000000000000000000)
  directionLo := (46088859896247680043/10000000000000000000)
  directionHi := (460888598962476800431/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree086.table
  base := (15940489308421495307102461692137799276179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-181057752366056188771908267216405297000000000000)
      constant := (4007634614302304872647630019258755214530311271931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree086.table
  base := (498140223081539996972784112243393466783/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-40030544963546651082733586246205750000000000)
      constant := (888122548580881330931164223925907531256820664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46088859896247680043/10000000000000000000)
  centralHi := (460888598962476800431/100000000000000000000)
  directionLo := (463591781079878003973/100000000000000000000)
  directionHi := (231795890539939001987/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree087.table
  base := (1062020040943219037766463529362970141011/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-45790633548699904497301685444068898000000000000)
      constant := (1025838751844341270300927733008022963901421911916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree087.table
  base := (8496159397752627602942938495388797209553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-8999088248454476864702285985283500000000000)
      constant := (202073966688302258139962934015474362393560817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463591781079878003973/100000000000000000000)
  centralHi := (231795890539939001987/50000000000000000000)
  directionLo := (466279292180161369077/100000000000000000000)
  directionHi := (233139646090080684539/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree088.table
  base := (18067490899549616389857598720292373924993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-185267316023543047206505216336145887000000000000)
      constant := (4200214677779620158852775968443742090352158688377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree088.table
  base := (18067489306038225114506831288710016773563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-163844997090174562798347950485383000000000000)
      constant := (3723182264226760762089280586502878753628037363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466279292180161369077/100000000000000000000)
  centralHi := (233139646090080684539/50000000000000000000)
  directionLo := (468951401690250902789/100000000000000000000)
  directionHi := (46895140169025090279/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree089.table
  base := (4791499957836687016084837424784359606771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-46843024463071619105950922724004045500000000000)
      constant := (1074553406222161870030753291737856142585015910619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree089.table
  base := (19165998466009738200996051527480188835319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-165706405708168542032054753235663000000000000)
      constant := (3810042785304365498270282874782617971160664719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468951401690250902789/100000000000000000000)
  centralHi := (46895140169025090279/10000000000000000000)
  directionLo := (471608371404144838787/100000000000000000000)
  directionHi := (117902092851036209697/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree090.table
  base := (10143923636204450587264580619920313650499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-94738439840514952820551082727943238500000000000)
      constant := (2198675924089734524494293502252032160049585946411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree090.table
  base := (20287846102716859322679649906763287807869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-18618646036240280140640172887327000000000000)
      constant := (433101440352561613417360543883234590176474141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471608371404144838787/100000000000000000000)
  centralHi := (117902092851036209697/25000000000000000000)
  directionLo := (474250455782267626609/100000000000000000000)
  directionHi := (47425045578226762661/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree091.table
  base := (10716516536041712626820452620758058790047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-95790830754886667429200320007878386000000000000)
      constant := (2248814673603973721893760215747424477342790870183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree091.table
  base := (21433032070121328041750823518308350894871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-169429222944156500499468358736223000000000000)
      constant := (3986792797452982314148431152637998020677559471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474250455782267626609/100000000000000000000)
  centralHi := (47425045578226762661/10000000000000000000)
  directionLo := (476877902235894490319/100000000000000000000)
  directionHi := (5960973777948681129/1250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree092.table
  base := (11300778551471268217380115585704794253221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-96843221669258382037849557287813533500000000000)
      constant := (2299523060799207108303692893588010660685184044669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree092.table
  base := (5650389061189736133775386914579649190589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-42822657890537619933293790371625750000000000)
      constant := (1019170571955754623676734418898675667544721989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476877902235894490319/100000000000000000000)
  centralHi := (5960973777948681129/1250000000000000000)
  directionLo := (479490951397548382707/100000000000000000000)
  directionHi := (119872737849387095677/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree093.table
  base := (23793419257228325013369766414546915052557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-195791225167260193292997589135497362000000000000)
      constant := (4701602171033189459185302155032474966875377713573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree093.table
  base := (11896709261137876292115326883274594950027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-9619557787785803275937886902043500000000000)
      constant := (231532301889541023461524606910779357940557803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479490951397548382707/100000000000000000000)
  centralHi := (119872737849387095677/25000000000000000000)
  directionLo := (48208983737820575153/10000000000000000000)
  directionHi := (482089837378205751531/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree094.table
  base := (12504309721920595918921136480690297406541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-98948003498001811255148031847683828500000000000)
      constant := (2402648747621851722678973971293940502190952050149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree094.table
  base := (5001723762898995714640852797038328739329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-175013448798138438200588766987063000000000000)
      constant := (4259490235789794308774902882727815465254973645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48208983737820575153/10000000000000000000)
  centralHi := (482089837378205751531/100000000000000000000)
  directionLo := (484674788012089225253/100000000000000000000)
  directionHi := (242337394006044612627/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree095.table
  base := (26247157585788649205107422950818591878541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-200000788824747051727594538255237952000000000000)
      constant := (4910132094002975469045266250048560474837616058149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree095.table
  base := (6561789261733351761859459853689164525487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-44218714354033104358573892434335750000000000)
      constant := (1088102173240863827677985791229623016930791687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484674788012089225253/100000000000000000000)
  centralHi := (242337394006044612627/50000000000000000000)
  directionLo := (243623012544885828663/50000000000000000000)
  directionHi := (487246025089771657327/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree096.table
  base := (27509033618024122997882004227745068365661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-202105570653490480944893012815108247000000000000)
      constant := (5016105967119242440604409729775350082853053171829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree096.table
  base := (13754516578349168474822470750418115322707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-9929792557451466481555687360423500000000000)
      constant := (247018711409396528481586763571446835328262323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243623012544885828663/50000000000000000000)
  centralHi := (487246025089771657327/100000000000000000000)
  directionLo := (122450941145066631487/25000000000000000000)
  directionHi := (489803764580266525949/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree097.table
  base := (449910116962752353083054770059456053661/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-51052588120558477540547871843744635500000000000)
      constant := (1280804778607640379833708499036523881460752461264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree097.table
  base := (1439712354535340740813788453489293432657/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-45149418663030093975427293809475750000000000)
      constant := (1135318643217193038171516396994454761091704285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122450941145066631487/25000000000000000000)
  centralHi := (489803764580266525949/100000000000000000000)
  directionLo := (49234821684273409727/10000000000000000000)
  directionHi := (492348216842734097271/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree098.table
  base := (1204111965687899248667056656277918399333/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-206315134310977339379489961934848837000000000000)
      constant := (5231471535800237923231934539425306115399280615925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree098.table
  base := (30102798804177775366760796874095147745907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-182459083270114355135415977988183000000000000)
      constant := (4637221995345883679969693360825045479287104107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49234821684273409727/10000000000000000000)
  centralHi := (492348216842734097271/100000000000000000000)
  directionLo := (49487958682839068729/10000000000000000000)
  directionHi := (494879586828390687291/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree099.table
  base := (3143468854865130368220343962389541956321/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-104209958069860384298394218247359566000000000000)
      constant := (2670431615556475905779634294216119392344842102845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree099.table
  base := (3143468825935528434538374228639856579437/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-10240027327117129687173487818803500000000000)
      constant := (263009948483459383862240389539663592757286465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49487958682839068729/10000000000000000000)
  centralHi := (494879586828390687291/100000000000000000000)
  directionLo := (99479614854633899401/20000000000000000000)
  directionHi := (248699037136584748503/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree100.table
  base := (16394957835999182337195910490227382151467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-105262348984232098907043455527294713500000000000)
      constant := (2725697100135738705188695346293415615319536196563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree100.table
  base := (32789915424427483334153654566505973281609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-186181900506102313602829583488743000000000000)
      constant := (4832145804855185197592772077769282036505465009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99479614854633899401/20000000000000000000)
  centralHi := (248699037136584748503/50000000000000000000)
  directionLo := (499903873881645571571/100000000000000000000)
  directionHi := (124975968470411392893/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree101.table
  base := (17084240242227139342753909940517405371217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-10421991951632566759699313087661000000000000)
      constant := (272672504812954802391882736805723342652281713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree101.table
  base := (34168480272611259421365709069611411713723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-188043309124096292836536386239023000000000000)
      constant := (4931122191734969667503684310089917281867393523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499903873881645571571/100000000000000000000)
  centralHi := (124975968470411392893/25000000000000000000)
  directionLo := (502397175502704198349/100000000000000000000)
  directionHi := (10047943510054083967/2000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree102.table
  base := (3557038296263102242231815512797997679587/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (775276)
      previous := (387638)
      next := (387638)
      square := (3579982901990305837677808230695000000000000)
      linear := (-371512563366697329149972076426176500000000000)
      constant := (9819851141542009068204405690086734871647334935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree102.table
  base := (7114076556275450929858297765774440404317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (152)
      previous := (76)
      next := (76)
      square := (701888619153084175605883390000000000000)
      linear := (-73012194441403411022777081503000000000000)
      constant := (1934297667544415016995391040424872202021585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502397175502704198349/100000000000000000000)
  centralHi := (10047943510054083967/2000000000000000000)
  directionLo := (252439082148700642459/50000000000000000000)
  directionHi := (504878164297401284919/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree103.table
  base := (7399124617372116126699371042982259367633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-216839043454694485465982334734200312000000000000)
      constant := (5789822750065626440031989038253857329309329016685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree103.table
  base := (7399124586358743705433267234646127772201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-191766126360084251303949991739583000000000000)
      constant := (5132103929450105089670276561332386891677474005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252439082148700642459/50000000000000000000)
  centralHi := (504878164297401284919/100000000000000000000)
  directionLo := (253673510449717870963/50000000000000000000)
  directionHi := (507347020899435741927/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree104.table
  base := (38444200840622077079402450275866436305587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-218943825283437914683280809294070607000000000000)
      constant := (5904910813908234460716270863205866324341701673243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree104.table
  base := (7688840141594199894620692024905679220759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-193627534978078230537656794489863000000000000)
      constant := (5234109280194885575134990162317610358265970795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253673510449717870963/50000000000000000000)
  centralHi := (507347020899435741927/100000000000000000000)
  directionLo := (25490196078431372549/5000000000000000000)
  directionHi := (509803921568627450981/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree105.table
  base := (39916116210056576503018463578378906154787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-221048607112181343900579283853940902000000000000)
      constant := (6021138151298247928892069515852419341691959852043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree105.table
  base := (39916116096591259176231577564993992273593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-21720993732896912196818177471127000000000000)
      constant := (593013809498080579794730743523493263767068377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25490196078431372549/5000000000000000000)
  centralHi := (509803921568627450981/100000000000000000000)
  directionLo := (512249038337769855821/100000000000000000000)
  directionHi := (256124519168884927911/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree106.table
  base := (20705684591778079849254672713569621163327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-111576694470462386558938879206905598500000000000)
      constant := (3069252381100722832817886238163910599385771532103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree106.table
  base := (10352842271627588717854112516763317689809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-49337588053516547251267599997605750000000000)
      constant := (1360287236321159525847730498840938389311193209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512249038337769855821/100000000000000000000)
  centralHi := (256124519168884927911/50000000000000000000)
  directionLo := (102936507830640684417/20000000000000000000)
  directionHi := (257341269576601711043/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree107.table
  base := (10732489937853980189808944003127544396767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-56314542692417050583794058243420373000000000000)
      constant := (1564252661647304186149495334733449543514370428263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree107.table
  base := (85859919336841667712277789552705827121/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-49802940208015042059694300685175750000000000)
      constant := (1386545814894103886592693419667594982042715125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102936507830640684417/20000000000000000000)
  centralHi := (257341269576601711043/50000000000000000000)
  directionLo := (517104588009435027061/100000000000000000000)
  directionHi := (258552294004717513531/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree108.table
  base := (44471887905539269773475746681030436503391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-227362952598411631552474707533551787000000000000)
      constant := (6376655804437691698122437478901176269520845469799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree108.table
  base := (44471887834566677675722008458513511921433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-22341463272228238608053778387887000000000000)
      constant := (628025247593098238121279679590966404945294137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517104588009435027061/100000000000000000000)
  centralHi := (258552294004717513531/50000000000000000000)
  directionLo := (103903069015621727703/20000000000000000000)
  directionHi := (129878836269527159629/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree109.table
  base := (23018576819594196720303007367166856840017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-114733867213577530384886591046711041000000000000)
      constant := (3248720117863503426466759910643285731127128877513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree109.table
  base := (11509288394625466795980424132644577720381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-50733644517012031676547702060315750000000000)
      constant := (1439820212888069449438442854574609046650710981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103903069015621727703/20000000000000000000)
  centralHi := (129878836269527159629/25000000000000000000)
  directionLo := (104382993366322860897/20000000000000000000)
  directionHi := (260957483415807152243/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree110.table
  base := (47625756946772970806289689656319022630547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-231572516255898489987071656653292377000000000000)
      constant := (6619363940440681445319278276865262111107866674683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree110.table
  base := (952515137897721077629032069854920060149/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-102397993343021052969948805495771500000000000)
      constant := (2933672064602853131955446386977306176911188725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104382993366322860897/20000000000000000000)
  centralHi := (260957483415807152243/50000000000000000000)
  directionLo := (65537950770200674719/12500000000000000000)
  directionHi := (524303606161605397753/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree111.table
  base := (24618848911835647935569302552022537906329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-116838649042320959602185065606581336000000000000)
      constant := (3371213459282545137330841292855726389316231555281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree111.table
  base := (49237697779311651185419688756506646378797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-22961932811559565019289379304647000000000000)
      constant := (664046340142967267651197665079612420803472333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65537950770200674719/12500000000000000000)
  centralHi := (524303606161605397753/100000000000000000000)
  directionLo := (263340706246339071189/50000000000000000000)
  directionHi := (526681412492678142379/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree112.table
  base := (12718244066519713068979926750877235579893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-58945519978346337105417151443258241750000000000)
      constant := (1716657292522254322032939433168292559563491174477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree112.table
  base := (50872976228157530071898612626280338381249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-208518803922030064407311216492103000000000000)
      constant := (6086499647785856676012195043035931160129628649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263340706246339071189/50000000000000000000)
  centralHi := (526681412492678142379/100000000000000000000)
  directionLo := (132262132972863151623/25000000000000000000)
  directionHi := (529048531891452606493/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree113.table
  base := (52531592270880142226684834616308414311863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-237886861742128777638967080332903262000000000000)
      constant := (6991970695003277720953640878507299063465245879807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree113.table
  base := (52531592238465240980633603712897306744563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-210380212540024043641018019242383000000000000)
      constant := (6197591888695465138058918285529639894842608363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132262132972863151623/25000000000000000000)
  centralHi := (529048531891452606493/100000000000000000000)
  directionLo := (531405107171280494131/100000000000000000000)
  directionHi := (132851276792820123533/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree114.table
  base := (54213545835540213150572392700576796830107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-239991643570872206856265554892773557000000000000)
      constant := (7118451493300398307331757055758839711390073315523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree114.table
  base := (27106772903917154199020467823890197685837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-11791201175445445715262490110703500000000000)
      constant := (350538543556071508788339857828498267131206893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531405107171280494131/100000000000000000000)
  centralHi := (132851276792820123533/25000000000000000000)
  directionLo := (533751277992792134977/100000000000000000000)
  directionHi := (266875638996396067489/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree115.table
  base := (55918836958012868934854536159417574523651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-242096425399615636073564029452643852000000000000)
      constant := (7246071564974346679014330544303927630984855752939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree115.table
  base := (55918836934333673435811865656479906534369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-214103029776012002108431624742943000000000000)
      constant := (6422805333722300052237301469229574236895893769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533751277992792134977/100000000000000000000)
  centralHi := (266875638996396067489/50000000000000000000)
  directionLo := (107217436192096597191/20000000000000000000)
  directionHi := (134021795240120746489/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree116.table
  base := (57647465636663012965117476878284200514131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-244201207228359065290862504012514147000000000000)
      constant := (7374830910020302425658470813953737407409503945659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree116.table
  base := (57647465616426807641789581891885901523191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-215964438394005981342138427493223000000000000)
      constant := (6536926537830507309696410502865123229861819791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107217436192096597191/20000000000000000000)
  centralHi := (134021795240120746489/25000000000000000000)
  directionLo := (538412949715528660309/100000000000000000000)
  directionHi := (53841294971552866031/10000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree117.table
  base := (5939943187020096022288924357136796199419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-123152994528551247254080489286192221000000000000)
      constant := (3752364764217231720523877924676130259166244801455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree117.table
  base := (11879886370581680123633006455507906906443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-24202871890222217841760581138167000000000000)
      constant := (739117488481197102024749244152082925479810135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538412949715528660309/100000000000000000000)
  centralHi := (53841294971552866031/10000000000000000000)
  directionLo := (67591089378125866303/12500000000000000000)
  directionHi := (21629148601000277217/4000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree118.table
  base := (61174735657626886170541651142326528507931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-248410770885845923725459453132254737000000000000)
      constant := (7635767420213882153460873911927006199102417793859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree118.table
  base := (61174735642850845280757513902841238548387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-219687255629993939809552032993783000000000000)
      constant := (6768197909220687171790345544469974061464354587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67591089378125866303/12500000000000000000)
  centralHi := (21629148601000277217/4000000000000000000)
  directionLo := (271517302433847628691/50000000000000000000)
  directionHi := (543034604867695257383/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree119.table
  base := (62973376998183860142454675721599071431123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 102010000000000000000000000000000000000000000
      center := (1550552)
      previous := (775276)
      next := (775276)
      square := (7159965803980611675355616461390000000000000)
      linear := (-866835822541831671082207362256488000000000000)
      constant := (26878700987392135169303626059267767252668885723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree119.table
  base := (62973376985559016665098568319089424940317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1368)
      previous := (684)
      next := (684)
      square := (6316997572377757580452950510000000000000)
      linear := (-766604374560511830599511542367000000000000)
      constant := (23824733828714321973586972608109804824462853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271517302433847628691/50000000000000000000)
  centralHi := (543034604867695257383/100000000000000000000)
  directionLo := (68166343064575391823/12500000000000000000)
  directionHi := (109066148903320626917/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree120.table
  base := (32397677945659074093158306204368623507093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-126310167271666391080028201125997663500000000000)
      constant := (3950630511930082857738820622584069135906402295277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree120.table
  base := (16198838970133017650286456055098280072511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-6205835357388386063249045513731750000000000)
      constant := (194541886060075746062925877983983402940955679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68166343064575391823/12500000000000000000)
  centralHi := (109066148903320626917/20000000000000000000)
  directionLo := (547617256618389849799/100000000000000000000)
  directionHi := (2738086283091949249/500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree121.table
  base := (13328134467329134257833736043684511562833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-254725116372076211377354876811865622000000000000)
      constant := (8035716735724265808994319214370040182668803880685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree121.table
  base := (66640672327431183716342189883947037553967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-225271481483975877510672441244623000000000000)
      constant := (7122677374212669315894414119937964244677868167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547617256618389849799/100000000000000000000)
  centralHi := (2738086283091949249/500000000000000000)
  directionLo := (68736782658726266091/12500000000000000000)
  directionHi := (549894261269810128729/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree122.table
  base := (34254663166961837606799968865402984537841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-128414949100409820297326675685867958500000000000)
      constant := (4085655860473955841690883626927294573783179135849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree122.table
  base := (68509326326052321487414257927589790314181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-227132890101969856744379243994903000000000000)
      constant := (7242856504647735729458848488686417044607184781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68736782658726266091/12500000000000000000)
  centralHi := (549894261269810128729/100000000000000000000)
  directionLo := (552161876091322485449/100000000000000000000)
  directionHi := (11043237521826449709/2000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree123.table
  base := (35200658941513406224579715936347069990823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-129467340014781534905975912965803106000000000000)
      constant := (4154022989765366901511623761913593841784675387247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree123.table
  base := (17600329469075815254691585787201422440743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-6360952742221217666057945742921750000000000)
      constant := (204556813596324617422421953790472711085374727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552161876091322485449/100000000000000000000)
  centralHi := (11043237521826449709/2000000000000000000)
  directionLo := (27721010814899396801/5000000000000000000)
  directionHi := (554420216297987936021/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree124.table
  base := (72316646983926959025155162614209162621901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-261039461858306499029250300491476507000000000000)
      constant := (8445919511472649255950126616611753059024837497189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree124.table
  base := (72316646978184213753225725798464412122957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-230855707337957815211792849495463000000000000)
      constant := (7486243728672521359102233419182277935931811157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27721010814899396801/5000000000000000000)
  centralHi := (554420216297987936021/100000000000000000000)
  directionLo := (139167348691944999679/25000000000000000000)
  directionHi := (556669394767779998717/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree125.table
  base := (74255313636676192499344349099644141709781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-263144243687049928246548775051346802000000000000)
      constant := (8584932316773811571437575454638165188714046558509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree125.table
  base := (14851062726354298739960779696340133158257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-232717115955951794445499652245743000000000000)
      constant := (7609451822262439617881416629128153431723132285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139167348691944999679/25000000000000000000)
  centralHi := (556669394767779998717/100000000000000000000)
  directionLo := (558909522107420578007/100000000000000000000)
  directionHi := (69863690263427572251/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree126.table
  base := (15243463568278489036859513786587208512699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-265249025515793357463847249611217097000000000000)
      constant := (8725084395434568424439027919464236996784971411055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree126.table
  base := (76217317837203761771379385704161209597569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-26064280508216197075467383888447000000000000)
      constant := (859296618915311295619904112059314589573697441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558909522107420578007/100000000000000000000)
  centralHi := (69863690263427572251/12500000000000000000)
  directionLo := (280570353357925190927/50000000000000000000)
  directionHi := (112228141343170076371/20000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree127.table
  base := (78202659598247421015609782600713589695367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-267353807344536786681145724171087392000000000000)
      constant := (8866375747455426013438268222556033273056424803663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree127.table
  base := (78202659594670448815761771612188492888909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-236439933191939752912913257746303000000000000)
      constant := (7858896972599100196830547285763948270004052309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280570353357925190927/50000000000000000000)
  centralHi := (112228141343170076371/20000000000000000000)
  directionLo := (563363054845436927729/100000000000000000000)
  directionHi := (56336305484543692773/10000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree128.table
  base := (40105669453728213725398124274483934113057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-134729294586640107949222099365478843500000000000)
      constant := (4504403186418509541991207532335168714835428098073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree128.table
  base := (40105669452201010444617950800654888348327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-119150670904966866073310030248291500000000000)
      constant := (3992567014673467334424022171846135364593998527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563363054845436927729/100000000000000000000)
  centralHi := (56336305484543692773/10000000000000000000)
  directionLo := (141394167665254482083/25000000000000000000)
  directionHi := (565576670661017928333/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree129.table
  base := (20560838942317456787293339663296525367631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-67890842750505911278935668322706995500000000000)
      constant := (2288094067895021431868352462053740679830783907159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree129.table
  base := (82243355766661801950125628869136093592653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-26684750047547523486702984805207000000000000)
      constant := (901375637831332220249692058276198331048276717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell079.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141394167665254482083/25000000000000000000)
  centralHi := (565576670661017928333/100000000000000000000)
  directionLo := (113556331259374578279/20000000000000000000)
  directionHi := (141945414074218222849/25000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree130.table
  base := (42149355091982929695460152429694361188977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-136834076415383537166520573925349138500000000000)
      constant := (4648542721842723109036258383497430287083250014953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree130.table
  base := (21074677545434778217630909443231614726723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-60506039761480422653508416499285750000000000)
      constant := (2060159276501254665154103225039430429904206523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113556331259374578279/20000000000000000000)
  centralHi := (141945414074218222849/25000000000000000000)
  directionLo := (142494527977927774771/25000000000000000000)
  directionHi := (113995622382342219817/20000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree131.table
  base := (86377402151844619493056203460920248349923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-275772934659510503550339622410568572000000000000)
      constant := (9442933889153985263482791390544160739162676147147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree131.table
  base := (21594350537485880671919098443860221349437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-60971391915978917461935117186855750000000000)
      constant := (2092475781479206473255368881844179935729885637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142494527977927774771/25000000000000000000)
  centralHi := (113995622382342219817/20000000000000000000)
  directionLo := (71520766967719966549/12500000000000000000)
  directionHi := (572166135741759732393/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree132.table
  base := (88479431673223016926306803639380503295649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-277877716488253932767638096970438867000000000000)
      constant := (9589921607986637141028876122041896657580366564761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree132.table
  base := (11059928958950004920982337483963982013867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-6826304896719712474484646430491750000000000)
      constant := (236116077783840472921741588020357181604015126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71520766967719966549/12500000000000000000)
  centralHi := (572166135741759732393/100000000000000000000)
  directionLo := (114869164830406351471/20000000000000000000)
  directionHi := (143586456038007939339/25000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree133.table
  base := (18120959749686112064744415980546396664061/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-279982498316997361984936571530309162000000000000)
      constant := (9738048600184373271487270627785272976599774647145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree133.table
  base := (90604798747045093903253559642313921404691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-247608384899903628315154074247983000000000000)
      constant := (8631464128910187114110745816539212509573601291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114869164830406351471/20000000000000000000)
  centralHi := (143586456038007939339/25000000000000000000)
  directionLo := (288258635842924638277/50000000000000000000)
  directionHi := (115303454337169855311/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree134.table
  base := (46376751688902920428440722067494305730451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-141043640072870395601117523045089728500000000000)
      constant := (4943657432874095925883202642288010209286579558139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree134.table
  base := (5797093961038949627612004969012155049831/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-62367448379474401887215219249565750000000000)
      constant := (2190939777998378056114497569646565461138441724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288258635842924638277/50000000000000000000)
  centralHi := (115303454337169855311/20000000000000000000)
  directionLo := (115736114222538871267/20000000000000000000)
  directionHi := (36167535694543397271/6250000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree135.table
  base := (94925545561693605180366575090710130323579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-284192061974484220419533520650049752000000000000)
      constant := (10037720404679109225686439139151990260520509690531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree135.table
  base := (94925545560684142983960541310844181419137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-27925689126210176309174186638727000000000000)
      constant := (988562638829904688260988374886103968430130593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115736114222538871267/20000000000000000000)
  centralHi := (36167535694543397271/6250000000000000000)
  directionLo := (290417906737227926727/50000000000000000000)
  directionHi := (116167162694891170691/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree136.table
  base := (48560462650221162926837058122537458924459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (775276)
      previous := (387638)
      next := (387638)
      square := (3579982901990305837677808230695000000000000)
      linear := (-495323259175134341932235285830311500000000000)
      constant := (17628486534564278064648488047888023618488406259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree136.table
  base := (2428023132489518362419188106913889657303/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22500000000000000000000000000000000000000
      center := (342)
      previous := (171)
      next := (171)
      square := (1579249393094439395113237627500000000000)
      linear := (-219024749787098240498507337801750000000000)
      constant := (7812610762403109550494334270970250069157270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290417906737227926727/50000000000000000000)
  centralHi := (116167162694891170691/20000000000000000000)
  directionLo := (291491544065068735737/50000000000000000000)
  directionHi := (23319323525205498859/4000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree137.table
  base := (99339642594402191302628425779290843376011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-288401625631971078854130469769790342000000000000)
      constant := (10341949302646354725453666248443961517782540892979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree137.table
  base := (24834910648416712385039840586239879479513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-63763504842969886312495321312275750000000000)
      constant := (2291675496900247501725618955743416426526213313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291491544065068735737/50000000000000000000)
  centralHi := (23319323525205498859/4000000000000000000)
  directionLo := (1462806206997722913/250000000000000000)
  directionHi := (585122482799089165201/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree138.table
  base := (25395424360980862342507423788940267374023/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-72626601865178627017857236082415159250000000000)
      constant := (2623943165421186949939898145773561634152416092047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree138.table
  base := (101581697443295891053568747134700011783383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-28546158665541502720409787555487000000000000)
      constant := (1033670620917671943887492891341244303405397687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1462806206997722913/250000000000000000)
  centralHi := (585122482799089165201/100000000000000000000)
  directionLo := (146813520900705267351/25000000000000000000)
  directionHi := (117450816720564213881/20000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree139.table
  base := (51923544924677524329257063062100517543857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-146305594644728968644363709444765466000000000000)
      constant := (5325367647047180337910801126505124773227851839273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree139.table
  base := (51923544924409751665226102778738999820331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-129388418303933751858697445374831500000000000)
      constant := (4720189421656540865716805720515771138532680931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146813520900705267351/25000000000000000000)
  centralHi := (117450816720564213881/20000000000000000000)
  directionLo := (589377975105456345751/100000000000000000000)
  directionHi := (73672246888182043219/12500000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree140.table
  base := (1658372184547555163557485475030825186421/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-73678992779550341626506473362350306750000000000)
      constant := (2701709299969053747058270978804764195038171191504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree140.table
  base := (26533954952646632672009243920011374555731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-65159561306465370737775423374985750000000000)
      constant := (2394682938191000015077527531516579585219456331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589377975105456345751/100000000000000000000)
  centralHi := (73672246888182043219/12500000000000000000)
  directionLo := (118298848070575341853/20000000000000000000)
  directionHi := (295747120176438354633/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree141.table
  base := (27111971832333032852476963643595240619717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-74205188236736198930831092002317880500000000000)
      constant := (2741019594757830657268850529652553044979590870813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree141.table
  base := (21689577465788435429586036700601968261437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-29166628204872829131645388472247000000000000)
      constant := (1079788257401411150808570245767011844137776465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118298848070575341853/20000000000000000000)
  centralHi := (295747120176438354633/50000000000000000000)
  directionLo := (296801480455305951991/50000000000000000000)
  directionHi := (593602960910611903983/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree142.table
  base := (22156658480912012591244703030286377940551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-298925534775688224940622842569141817000000000000)
      constant := (11122458831560683623954953695865464012281905285195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree142.table
  base := (27695823101056833693857304913268177281139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-66090265615462360354628824750125750000000000)
      constant := (2464616633715017320649129052890489529108242539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296801480455305951991/50000000000000000000)
  centralHi := (593602960910611903983/100000000000000000000)
  directionLo := (59570421690052203799/10000000000000000000)
  directionHi := (595704216900522037991/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree143.table
  base := (22628407007412387877077729312015032544247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-301030316604431654157921317129012112000000000000)
      constant := (11281978557465284445546201585226363605516682969915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree143.table
  base := (28285508759194513336549024029424879709011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-66555617769960855163055525437695750000000000)
      constant := (2499962101876745225433689754555567612123137611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59570421690052203799/10000000000000000000)
  centralHi := (595704216900522037991/100000000000000000000)
  directionLo := (74724760879539931629/12500000000000000000)
  directionHi := (597798087036319453033/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree144.table
  base := (5776205761358366501539767191424811300153/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-75783774608293770843804947922220601750000000000)
      constant := (2860659389186524173393914088683114789605283788085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree144.table
  base := (115524115226925128258063348411695860360371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-29787097744204155542880989389007000000000000)
      constant := (1126915548283810623724624784084228103644147219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74724760879539931629/12500000000000000000)
  centralHi := (597798087036319453033/100000000000000000000)
  directionLo := (119976929731594937177/20000000000000000000)
  directionHi := (299942324328987342943/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree145.table
  base := (7370595810950025966427516122977864163051/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-76309970065479628148129566562188175500000000000)
      constant := (2901108957351019020304229524216493361986589438156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree145.table
  base := (117929532974993787201390039141942956891863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-269945288315831379119635707251343000000000000)
      constant := (10285641116002859335179732249009803630875735663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119976929731594937177/20000000000000000000)
  centralHi := (299942324328987342943/50000000000000000000)
  directionLo := (150490994441262267703/25000000000000000000)
  directionHi := (601963977765049070813/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree146.table
  base := (120358288281479730413148590739497188986551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-307344662090661941809816740808622997000000000000)
      constant := (11767373375440161677208409021064160355382172151039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree146.table
  base := (60179144140651729571871384086013536370503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-135903348466912679176671255000811500000000000)
      constant := (5215025975926751450726863660611355208099678303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150490994441262267703/25000000000000000000)
  centralHi := (601963977765049070813/100000000000000000000)
  directionLo := (302018074524497314121/50000000000000000000)
  directionHi := (604036149048994628243/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree147.table
  base := (61405190573158989464526447284220824405429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-154724721959702685513557607684246646000000000000)
      constant := (5965725097427637680456162852235645654563076775181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree147.table
  base := (61405190573083805879281178359611359265017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (21964)
      previous := (10982)
      next := (10982)
      square := (101422905467620663375050149855000000000000)
      linear := (-15203783641767740977058295152883500000000000)
      constant := (587526246783724535653457102743494682827589913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302018074524497314121/50000000000000000000)
  centralHi := (604036149048994628243/100000000000000000000)
  directionLo := (151525308981115019567/25000000000000000000)
  directionHi := (606101235924460078269/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree148.table
  base := (156607264462527386895729691556905924793/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-77888556437037200061103422482090896750000000000)
      constant := (3024166571912580363556265836206331486433414115400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree148.table
  base := (25057162313978729120945669471924097386769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-275529514169813316820756115502183000000000000)
      constant := (10721902586764275104958879523730796886514930845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151525308981115019567/25000000000000000000)
  centralHi := (606101235924460078269/100000000000000000000)
  directionLo := (304079655279820051529/50000000000000000000)
  directionHi := (608159310559640103059/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree149.table
  base := (63892289776446119975477372318985048187293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-156829503788446114730856082244116941000000000000)
      constant := (6131510826913093249955916781843634861037928433077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree149.table
  base := (255569159105565670410773073988934170481/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-69347730696951824013615729563115750000000000)
      constant := (2717335596456496726519596140501632722177635125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304079655279820051529/50000000000000000000)
  centralHi := (608159310559640103059/100000000000000000000)
  directionLo := (610210443905703354503/100000000000000000000)
  directionHi := (76276305488212919313/12500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree150.table
  base := (13030668509522362305855416327551968615961/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-157881894702817829339505319524052088500000000000)
      constant := (6215258146691869580364465300944507553025299242645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree150.table
  base := (130306685095130308731579035952385105005113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-31028036822866808365352191222527000000000000)
      constant := (1224199093254771630388180388130539295346477657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610210443905703354503/100000000000000000000)
  centralHi := (76276305488212919313/12500000000000000000)
  directionLo := (122450941145066631487/20000000000000000000)
  directionHi := (153063676431333289359/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree151.table
  base := (66426064098652323074528934339748067376047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-158934285617189543948154556803987236000000000000)
      constant := (6299575103161915108874774727225459297765083024183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree151.table
  base := (6642606409861252965637036058525424530767/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-70278435005948813630469130938255750000000000)
      constant := (2791812736791475019583564108037312646022624835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122450941145066631487/20000000000000000000)
  centralHi := (153063676431333289359/25000000000000000000)
  directionLo := (153573041155103347497/25000000000000000000)
  directionHi := (614292164620413389989/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree152.table
  base := (135420908859417857938801544270036275353151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-319973353063122517113607588167844767000000000000)
      constant := (12768923392647292649736283469971367966969595578439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree152.table
  base := (67710454429674991054473288920692793198143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-141487574320894616877791663251651500000000000)
      constant := (5658859854722794465455819207707769955108369943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153573041155103347497/25000000000000000000)
  centralHi := (614292164620413389989/100000000000000000000)
  directionLo := (24652915522355625067/4000000000000000000)
  directionHi := (154080722014722656669/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree153.table
  base := (69006513540919908894743104647809130786687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 51005000000000000000000000000000000000000000
      center := (775276)
      previous := (387638)
      next := (387638)
      square := (3579982901990305837677808230695000000000000)
      linear := (-557228607079352848323366890532379000000000000)
      constant := (22387259260129657055884447135961228255654994087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree153.table
  base := (17251628385222741527524705357370018978069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (175472154788271043901470847500000000000)
      linear := (-27377600659340947038570754445750000000000)
      constant := (1102383518467198320967019621293240037956138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24652915522355625067/4000000000000000000)
  centralHi := (154080722014722656669/25000000000000000000)
  directionLo := (3091734712004211513/500000000000000000)
  directionHi := (618346942400842302601/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree154.table
  base := (140628482864841162917161768721000676962087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-324182916720609375548204537287585357000000000000)
      constant := (13111887585447575466043957726571234657744482101743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree154.table
  base := (140628482864791799302511768201455883867993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-286697965877777192222996932003863000000000000)
      constant := (11621686197228031863617260038702598753940649793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3091734712004211513/500000000000000000)
  centralHi := (618346942400842302601/100000000000000000000)
  directionLo := (310182196461889697481/50000000000000000000)
  directionHi := (620364392923779394963/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree155.table
  base := (143267276208686689928556302266543299294157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-326287698549352804765503011847455652000000000000)
      constant := (13285078591925974356928057693743017881797812015973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree155.table
  base := (71633638104322297715786212674552796770887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-144279687247885585728351867377071500000000000)
      constant := (5887591961366089912074827410519406824401077087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310182196461889697481/50000000000000000000)
  centralHi := (620364392923779394963/100000000000000000000)
  directionLo := (622375303847210917161/100000000000000000000)
  directionHi := (311187651923605458581/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree156.table
  base := (72964703556817723817472622417675568635461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-164196240189048116991400743203662973500000000000)
      constant := (6729704435895451074952247265854499772962947584029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree156.table
  base := (3648235177839988833029476860455663581453/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (10982)
      previous := (5491)
      next := (5491)
      square := (50711452733810331687525074927500000000000)
      linear := (-8067243975382365296955848264011750000000000)
      constant := (331380313962384707700740246741834867750399170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622375303847210917161/100000000000000000000)
  centralHi := (311187651923605458581/50000000000000000000)
  directionLo := (624379738356496377971/100000000000000000000)
  directionHi := (156094934589124094493/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree157.table
  base := (18576859447492604824326997697963901615047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-82624315551709915800024990241799060500000000000)
      constant := (3408719606260776474566981784871798175153054590366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree157.table
  base := (148614875579910232481819395482731665208757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-292282191731759129924117340254703000000000000)
      constant := (12085208336969700331135020679576571061207976957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624379738356496377971/100000000000000000000)
  centralHi := (156094934589124094493/25000000000000000000)
  directionLo := (78297219828251408783/12500000000000000000)
  directionHi := (125275551725202254053/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree158.table
  base := (30264736321570145451550384089863437514807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-332602044035583092417398435527066537000000000000)
      constant := (13811487251683316328477432270001224714197949269115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree158.table
  base := (30264736321564926261592800198059515690763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-294143600349753109157824143004983000000000000)
      constant := (12241735025704377429698788274626768001558372815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78297219828251408783/12500000000000000000)
  centralHi := (125275551725202254053/20000000000000000000)
  directionLo := (628369425841649617659/100000000000000000000)
  directionHi := (31418471292082480883/5000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree159.table
  base := (154055825197607552944239988583198155642917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-334706825864326521634696910086936832000000000000)
      constant := (13989235351712248173225136054428845798596171535613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree159.table
  base := (154055825197585303422696861809775153146023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-32889445440860787599058993972807000000000000)
      constant := (1377696818761167961654621452898503019259200647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628369425841649617659/100000000000000000000)
  centralHi := (31418471292082480883/5000000000000000000)
  directionLo := (630354800222686620513/100000000000000000000)
  directionHi := (315177400111343310257/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree160.table
  base := (156811306349448446185663959094466259389431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-336811607693069950851995384646807127000000000000)
      constant := (14168122725130600514422764766851525260177128247359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree160.table
  base := (78405653174714738447399859912906040880669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (197676)
      previous := (98838)
      next := (98838)
      square := (912806149208585970375451348695000000000000)
      linear := (-148933208792870533812618874252771500000000000)
      constant := (6278908683204360018460168197298908612330620069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630354800222686620513/100000000000000000000)
  centralHi := (315177400111343310257/50000000000000000000)
  directionLo := (316166970521511751073/50000000000000000000)
  directionHi := (632333941043023502147/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree161.table
  base := (9974382816475334201012130221192175518519/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-84729097380453345017323464801669355500000000000)
      constant := (3587037342984764283130833287502150483785110640764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree161.table
  base := (31918025012717835036933742443551402072217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-299727826203735046858944551255823000000000000)
      constant := (12717373018379606068805508582964123983949182085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316166970521511751073/50000000000000000000)
  centralHi := (632333941043023502147/100000000000000000000)
  directionLo := (19822090832869867491/3125000000000000000)
  directionHi := (634306906651835759713/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree162.table
  base := (162392281340305125610513620845231555157183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-341021171350556809286592333766547717000000000000)
      constant := (14529315292138286859224399598030476889211784473287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree162.table
  base := (162392281340291338878450347484903892017677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-33509914980192114010294594889567000000000000)
      constant := (1430882036084862224779075189976901224793108653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19822090832869867491/3125000000000000000)
  centralHi := (634306906651835759713/100000000000000000000)
  directionLo := (636273754493645169373/100000000000000000000)
  directionHi := (318136877246822584687/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree163.table
  base := (165217775179769700246510584052304086013837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-343125953179300238503890808326418012000000000000)
      constant := (14711620485728943931128758105390366269757446707493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree163.table
  base := (10326110948734871715028875190527697248071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-75862660859930751331589539189095750000000000)
      constant := (3259878321390439817031382568438573662168930684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636273754493645169373/100000000000000000000)
  centralHi := (318136877246822584687/50000000000000000000)
  directionLo := (638234541127835080117/100000000000000000000)
  directionHi := (319117270563917540059/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree164.table
  base := (84033303291108079460718802680618301573601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-172615367504021833860594641443144153500000000000)
      constant := (7447532476355834171191761693650459734567815798489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree164.table
  base := (168066606582206140357319878905146459587559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-305312052057716984560064959506663000000000000)
      constant := (13202097900774168583951758011042277941387240959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638234541127835080117/100000000000000000000)
  centralHi := (319117270563917540059/50000000000000000000)
  directionLo := (64018932224762775279/10000000000000000000)
  directionHi := (640189322247627752791/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree165.table
  base := (42734693886964219269257944507891007887713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-86833879209196774234621939361539650500000000000)
      constant := (3769912173271771548673087677323136386208929930457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree165.table
  base := (170938775547848337167475278609754147183927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-34130384519523440421530195806327000000000000)
      constant := (1485076907822393385967763529133548948536154903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64018932224762775279/10000000000000000000)
  centralHi := (640189322247627752791/100000000000000000000)
  directionLo := (321069076349270879299/50000000000000000000)
  directionHi := (642138152698541758599/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree166.table
  base := (173834282076899635195438303859140680700177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29480890000000000000000000000000000000000000000
      center := (448109528)
      previous := (224054764)
      next := (224054764)
      square := (2069230117350396774177773157341710000000000000)
      linear := (-349440298665530526155786232006028897000000000000)
      constant := (15265371706855810043409067037182382832224704111753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree166.table
  base := (173834282076892355970646729023164384088311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-309034869293704943027478565007223000000000000)
      constant := (13530296094444415472277239415598478563013696911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321069076349270879299/50000000000000000000)
  centralHi := (642138152698541758599/100000000000000000000)
  directionLo := (80510135812043342841/12500000000000000000)
  directionHi := (644081086496346742729/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree167.table
  base := (88376563084773867258434967079837166778731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-175772540247136977686542353282949596000000000000)
      constant := (7726116997009219619341814970392002486734042295059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree167.table
  base := (22094140771192691261995872397008442927867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (98838)
      previous := (49419)
      next := (49419)
      square := (456403074604292985187725674347500000000000)
      linear := (-77724069477924730565296341939375750000000000)
      constant := (3423977418225830612410733812865179420110764134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80510135812043342841/12500000000000000000)
  centralHi := (644081086496346742729/100000000000000000000)
  directionLo := (129203635368906436423/20000000000000000000)
  directionHi := (161504544211133045529/25000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree168.table
  base := (22461913478250013850555576288026836634691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7370222500000000000000000000000000000000000000
      center := (112027382)
      previous := (56013691)
      next := (56013691)
      square := (517307529337599193544443289335427500000000000)
      linear := (-88412465580754346147595795281442371750000000000)
      constant := (3910058888643890065212748507189012129075059110998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree168.table
  base := (179695307825994822678109200586575065750261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (43928)
      previous := (21964)
      next := (21964)
      square := (202845810935241326750100299710000000000000)
      linear := (-34750854058854766832765796723087000000000000)
      constant := (1540281433975419878768916020989696194001825429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell079.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129203635368906436423/20000000000000000000)
  centralHi := (161504544211133045529/25000000000000000000)
  directionLo := (647949476151306120071/100000000000000000000)
  directionHi := (80993684518913265009/12500000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 3493
  qDenominator := 6868
  table := BinomialMassData.Q3493_6868.Degree169.table
  base := (18266082704645144594384967911141011957423/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14740445000000000000000000000000000000000000000
      center := (224054764)
      previous := (112027382)
      next := (112027382)
      square := (1034615058675198387088886578670855000000000000)
      linear := (-177877322075880406903840827842819891000000000000)
      constant := (7914688194263873524718426712846877843315236073235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3493_6868.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 26
  qDenominator := 51
  table := BinomialMassData.Q26_51.Degree169.table
  base := (182660827046446938949388770573429842314783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (395352)
      previous := (197676)
      next := (197676)
      square := (1825612298417171940750902697390000000000000)
      linear := (-314619095147686880728598973258063000000000000)
      constant := (14030165793071291278418418524344173019860750583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q26_51.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell079.Kernel169
