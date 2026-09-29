import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell055.Parameters
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch000_049
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch050_099
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch100_149
import ForestUnimodality.BinomialMassData.Q49_99.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_99.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_99.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree000.table
  base := (5591641030229401070460681957/100000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (105099763778102490985322248750000000000)
      linear := (600141645620005061340963837500000000)
      constant := (69895512877867513380758524462500000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree000.table
  base := (5591641030229401070460681957/100000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (105099763778102490985322248750000000000)
      linear := (600141645620005061340963837500000000)
      constant := (69895512877867513380758524462500000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree001.table
  base := (80327252928417287118051300966530093107379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (549606392506406048103842490523777500000000000)
      linear := (-539500225948720136431323494607780675000000000)
      constant := (210163175124881430302123833349325834541839690131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree001.table
  base := (160344604384692284817671877778311165394309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-4055183679625714791733574683204650000000000)
      constant := (1572535200557202369243214848919919882029622509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12498995418557205427/25000000000000000000)
  directionHi := (49995981674228821709/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree002.table
  base := (95714210010970056583357931706548991041241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-2164277638831858647380624152012358850000000000)
      constant := (251328213161076603158294956037288896911631389049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree002.table
  base := (95376538531972598582888900213313089354601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-8133895312326316261891960512694650000000000)
      constant := (938799676380179802848165730374055888764444401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/25000000000000000000)
  centralHi := (49995981674228821709/100000000000000000000)
  directionLo := (70704995347851118773/100000000000000000000)
  directionHi := (35352497673925559387/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree003.table
  base := (119378004332005061412955883968039694955779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-722123294614728227088578069957590300000000000)
      constant := (35215510607366037347409755291961232368247870859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree003.table
  base := (7426109084751030603688469456942879401083/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (15246)
      previous := (7623)
      next := (7623)
      square := (114453642754353612683015928888750000000000)
      linear := (-339239081806303270334731842838462500000000)
      constant := (16425439690378001187505056857945103835558774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70704995347851118773/100000000000000000000)
  centralHi := (35352497673925559387/50000000000000000000)
  directionLo := (21648895108511705121/25000000000000000000)
  directionHi := (17319116086809364097/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree004.table
  base := (78452346577252310287599014024830626881449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-8669664025401390792833156955211907700000000000)
      constant := (213675845072778276027679996832251210270029004361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree004.table
  base := (78029809266269645235182460036516207999939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-32582637155455038404417464343349300000000000)
      constant := (796977099633172590673878326383312554607402139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/25000000000000000000)
  centralHi := (17319116086809364097/20000000000000000000)
  directionLo := (12498995418557205427/12500000000000000000)
  directionHi := (99991963348457643417/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree005.table
  base := (1360359516942654750398622469502511832553/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (274803196253203024051921245261888750000000000)
      linear := (-1355027299908778442733638910100687837500000000)
      constant := (19454959383752440249003126710988581554730855085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree005.table
  base := (54105850672089067951733000005076472574959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-40740060420856241344734236002329300000000000)
      constant := (580643897518473665383984276276476007707173159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/12500000000000000000)
  centralHi := (99991963348457643417/100000000000000000000)
  directionLo := (55897206812704695447/50000000000000000000)
  directionHi := (22358882725081878179/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree006.table
  base := (19819272750479918065773386270882502065499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-722820709618836905050281422577727650000000000)
      constant := (6827367480349238998600756714108521907570834979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree006.table
  base := (39412688867269857258808535647343732898363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-5433053742917493809450111962367700000000000)
      constant := (50979916362400564371279760919513525126317307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55897206812704695447/50000000000000000000)
  centralHi := (22358882725081878179/20000000000000000000)
  directionLo := (122464644291399242379/100000000000000000000)
  directionHi := (6123232214569962119/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree007.table
  base := (30036013689261874660890680422073427430601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5976432)
      previous := (2988216)
      next := (2988216)
      square := (44865827959706616171742244124390000000000000)
      linear := (-309823003000161245713082039428422300000000000)
      constant := (2137625548701368034951277329365045011124299961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree007.table
  base := (7466598150127361525013875843815638831849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-14263726737914661806341944830072325000000000)
      constant := (97869134667137593206789441413554601190952049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122464644291399242379/100000000000000000000)
  centralHi := (6123232214569962119/5000000000000000000)
  directionLo := (132276934062552149927/100000000000000000000)
  directionHi := (16534616757819018741/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree008.table
  base := (23399012910835219811831169688801816575611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-17351881520876737788976974257586287700000000000)
      constant := (95420148759859820532642916883744239580267749979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree008.table
  base := (23266481430725583062245965799225698304253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-65212330217059850165684550979269300000000000)
      constant := (357048862936262399739857014056725469079983653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132276934062552149927/100000000000000000000)
  centralHi := (16534616757819018741/12500000000000000000)
  directionLo := (70704995347851118773/50000000000000000000)
  directionHi := (141409990695702237547/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree009.table
  base := (4631109590371353677154263112381946718763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (8134588)
      previous := (4067294)
      next := (4067294)
      square := (61067376945156227567093610058197500000000000)
      linear := (-542289885965154848278136905088330075000000000)
      constant := (2549343343594173949469544621368736217681745523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree009.table
  base := (9208087343922228874238715092060908900367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (50868285668601605636895968395000000000000)
      linear := (-452899712854697858679020510112650000000000)
      constant := (2122262794551529286293668285100719976944407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70704995347851118773/50000000000000000000)
  centralHi := (141409990695702237547/100000000000000000000)
  directionLo := (37496986255671616281/25000000000000000000)
  directionHi := (1199903560181491721/800000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree010.table
  base := (14747705611977291340917645859836936709503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-21692990268614411287048882908773477700000000000)
      constant := (92074605118265886447631134799698950958033689567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree010.table
  base := (29311040737393364444910213053201319379/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-20381794186965564011579523574307325000000000)
      constant := (86320369607185808895671068305039016404197375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37496986255671616281/25000000000000000000)
  centralHi := (1199903560181491721/800000000000000000)
  directionLo := (39525293986650372653/25000000000000000000)
  directionHi := (158101175946601490613/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree011.table
  base := (2923575314188878778438358133181872073969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54022500000000000000000000000000000000000000
      center := (605052)
      previous := (302526)
      next := (302526)
      square := (4542201590962033455403656946477500000000000)
      linear := (-49304844302651338917530655442907175000000000)
      constant := (196974477117001283214903105037015061146396121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree011.table
  base := (2903280468169446022774557030790303556449/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 202500000000000000000000000000000000000000
      center := (2268)
      previous := (1134)
      next := (1134)
      square := (17026161732052603539622204297500000000000)
      linear := (-185298760357982353278171210653325000000000)
      constant := (739325458652736445092153827886839588072369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39525293986650372653/25000000000000000000)
  centralHi := (158101175946601490613/100000000000000000000)
  directionLo := (20727239029862697319/12500000000000000000)
  directionHi := (165817912238901578553/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree012.table
  base := (4573565367560103464875807396229297274719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-1446338834241782488062266197775592650000000000)
      constant := (5610658390480925549378829305663242223548638599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree012.table
  base := (9073874618428739597704018976103508799807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-10871335919851629102994626401687700000000000)
      constant := (42150495932554618229542765896009121082989823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20727239029862697319/12500000000000000000)
  centralHi := (165817912238901578553/100000000000000000000)
  directionLo := (21648895108511705121/12500000000000000000)
  directionHi := (173191160868093640969/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree013.table
  base := (3487747223348187018818735024268731890357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-14102326695110460767078372942777131350000000000)
      constant := (54350739311472556732105427828177577617665653973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree013.table
  base := (1727075949338714579962429250691947682711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-26499861636016466216817102318542325000000000)
      constant := (102143830011227012169091525787140754238250511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/12500000000000000000)
  centralHi := (173191160868093640969/100000000000000000000)
  directionLo := (90131537746794981473/50000000000000000000)
  directionHi := (180263075493589962947/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree014.table
  base := (637112178056004150501459282826490887473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66701250000000000000000000000000000000000000
      center := (747054)
      previous := (373527)
      next := (373527)
      square := (5608228494963327021467780515548750000000000)
      linear := (-77487774908392240518348725028438412500000000)
      constant := (301655181185279678157232760537374186496446753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree014.table
  base := (2517323671945852541970675439628875784903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-57078434904733533903792590466574650000000000)
      constant := (222347370969538432059825785002582711567834303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90131537746794981473/50000000000000000000)
  centralHi := (180263075493589962947/100000000000000000000)
  directionLo := (23383479267549109491/12500000000000000000)
  directionHi := (187067834140392875929/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree015.table
  base := (3456380693669968522944977193151648336791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-3616195793106510559136517170749050300000000000)
      constant := (14387800845233023859692649060005358276452858111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree015.table
  base := (679674950789354497128825257642726901477/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-13590477008318696749766883621347700000000000)
      constant := (54130919511654149480650663836605147978542265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23383479267549109491/12500000000000000000)
  centralHi := (187067834140392875929/100000000000000000000)
  directionLo := (96816802200789717329/50000000000000000000)
  directionHi := (193633604401579434659/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree016.table
  base := (503806718447333378467399742047629341259/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (549606392506406048103842490523777500000000000)
      linear := (-8679079127956857945316152215583761925000000000)
      constant := (35581093615313805192894341524724147214667153451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree016.table
  base := (1961014119295312386326569502113101429153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-130471716340269473688218724251109300000000000)
      constant := (535648857869828735788252242717959307107128553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96816802200789717329/50000000000000000000)
  centralHi := (193633604401579434659/100000000000000000000)
  directionLo := (12498995418557205427/6250000000000000000)
  directionHi := (199983926696915286833/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree017.table
  base := (372350195303115823169061340093887718541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-18443435442848134265150281593964321350000000000)
      constant := (78338098498667249340683394870317467634904248749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree017.table
  base := (693968013624329486019004196012046259937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-138629139605670676628535495910089300000000000)
      constant := (589826205358607368571837576909927165393642537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/6250000000000000000)
  centralHi := (199983926696915286833/100000000000000000000)
  directionLo := (206138713299290317851/100000000000000000000)
  directionHi := (51534678324822579463/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree018.table
  base := (-377492727158648412491176189815496196551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-4339713917729456142148501945946915300000000000)
      constant := (19165264823762746355227279624945676379481806929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree018.table
  base := (-13280653180601496176323338636966574647/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12717071417150401409223992098750000000000)
      linear := (-226522473566468949951932511680662500000000)
      constant := (1002303342491506833817568822077883177870852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206138713299290317851/100000000000000000000)
  centralHi := (51534678324822579463/25000000000000000000)
  directionLo := (1325718662772208477/625000000000000000)
  directionHi := (212114986043553356321/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree019.table
  base := (-273852668215331907558783473470611988841/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-41227979633433942028372471839115832700000000000)
      constant := (189711102378114737240773480785988897597546572755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree019.table
  base := (-1413701293194031600614430793164689669999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-154943986136473082509169039228049300000000000)
      constant := (714472808799299239821819262619074576544339801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1325718662772208477/625000000000000000)
  centralHi := (212114986043553356321/100000000000000000000)
  directionLo := (54481857925268721573/25000000000000000000)
  directionHi := (217927431701074886293/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree020.table
  base := (-449076046676889588068391783221634767481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-43398534007302778777408426164709427700000000000)
      constant := (208308738117627004568353823436394451557249357955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree020.table
  base := (-2286938517759008217654398428357052291077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-163101409401874285449485810887029300000000000)
      constant := (784622414707696596068786740107558530495154323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54481857925268721573/25000000000000000000)
  centralHi := (217927431701074886293/100000000000000000000)
  directionLo := (55897206812704695447/25000000000000000000)
  directionHi := (223588827250818781789/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree021.table
  base := (-1509125999257855321406840407265074049767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (332024)
      previous := (166012)
      next := (166012)
      square := (2492545997761478676207902451355000000000000)
      linear := (-51665633085228589032249864501477350000000000)
      constant := (258784405915000306513896410326820975958931457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree021.table
  base := (-38213595502289892491396688726865502309/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (15246)
      previous := (7623)
      next := (7623)
      square := (114453642754353612683015928888750000000000)
      linear := (-2378594898156604005413924757583462500000000)
      constant := (11941943050423270195411548933276522179854990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55897206812704695447/25000000000000000000)
  centralHi := (223588827250818781789/100000000000000000000)
  directionLo := (114555185232889292003/50000000000000000000)
  directionHi := (229110370465778584007/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree022.table
  base := (-3698444608213122546111790584722989736483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (2420208)
      previous := (1210104)
      next := (1210104)
      square := (18168806363848133821614627785910000000000000)
      linear := (-394542502107772332855209378643773700000000000)
      constant := (2061990077241608691549714981597613564784338853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree022.table
  base := (-1867353042948079369293245847474599659099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (4536)
      previous := (2268)
      next := (2268)
      square := (34052323464105207079244408595000000000000)
      linear := (-741389487325110294752559314896650000000000)
      constant := (3884139629095043486922975673915857427612981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114555185232889292003/50000000000000000000)
  centralHi := (229110370465778584007/100000000000000000000)
  directionLo := (234501940372646238431/100000000000000000000)
  directionHi := (7328185636645194951/3125000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree023.table
  base := (-2147520889899963861994404620070537613291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-24955098564454644512258144570745106350000000000)
      constant := (136021923504737976420587277307705931503441768501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree023.table
  base := (-4328871366278476497938161940853108077889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-187573679198077894270436125863969300000000000)
      constant := (1024959117850230875427607011812477587728609911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234501940372646238431/100000000000000000000)
  centralHi := (7328185636645194951/3125000000000000000)
  directionLo := (239772304952231620333/100000000000000000000)
  directionHi := (119886152476115810167/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree024.table
  base := (-4815908025796797362391201202141139998497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-5786750166975347308172471496342645300000000000)
      constant := (32872936194708445845969176035905016066496653063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree024.table
  base := (-4847442759299348859435660282001289144761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-21747900273719899690083655280327700000000000)
      constant := (123859428186087815406434976542645396121355271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239772304952231620333/100000000000000000000)
  centralHi := (119886152476115810167/50000000000000000000)
  directionLo := (244929288582798484759/100000000000000000000)
  directionHi := (6123232214569962119/2500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree025.table
  base := (-1053577722844264364805218696852777560319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-54251305876646962522588197792677402700000000000)
      constant := (320920637327947185667283266672603356967935371045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree025.table
  base := (-42378084805292811004876794410354707163/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-203888525728880300151069669181929300000000000)
      constant := (1209221955584455520285930910376621689386929625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244929288582798484759/100000000000000000000)
  centralHi := (6123232214569962119/2500000000000000000)
  directionLo := (12498995418557205427/5000000000000000000)
  directionHi := (249979908371144108541/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree026.table
  base := (-1131393319646114571493401133228243641329/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-56421860250515799271624152118270997700000000000)
      constant := (347220837912913261228650654327638348258485591595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree026.table
  base := (-5684303018246799613570378351328305367403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-212045948994281503091386440840909300000000000)
      constant := (1308361831947859196188406352236123079094083197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/5000000000000000000)
  centralHi := (249979908371144108541/100000000000000000000)
  directionLo := (50986097231624006123/20000000000000000000)
  directionHi := (31866310769765003827/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree027.table
  base := (-2994194618677631025276559675443809325841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-3255134145799146445592228135770255150000000000)
      constant := (20819072641972174585940505854532461245847346839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree027.table
  base := (-3006906125255990861486716776174815442907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (50868285668601605636895968395000000000000)
      linear := (-1359280075677053740936439583332650000000000)
      constant := (8716685824604221823830667808936897331408253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50986097231624006123/20000000000000000000)
  centralHi := (31866310769765003827/12500000000000000000)
  directionLo := (64946685325535115363/25000000000000000000)
  directionHi := (259786741302140461453/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree028.table
  base := (-6266771676015271686756144085072431699079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5976432)
      previous := (2988216)
      next := (2988216)
      square := (44865827959706616171742244124390000000000000)
      linear := (-1240060591801091281014205321825677300000000000)
      constant := (8234203654864423510902658348404721872105445481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree028.table
  base := (-6290398315449403960381406027365133042061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-228360795525083908972019984158869300000000000)
      constant := (1520400587712187634531845963164994731054760139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64946685325535115363/25000000000000000000)
  centralHi := (259786741302140461453/100000000000000000000)
  directionLo := (132276934062552149927/50000000000000000000)
  directionHi := (52910773625020859971/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree029.table
  base := (-812022892390880509594822211623684572543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (274803196253203024051921245261888750000000000)
      linear := (-7866690421515288689841501886881472837500000000)
      constant := (54176026594232317757709750730584321783702115873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree029.table
  base := (-6518125237303933131545278790003751377809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-236518218790485111912336755817849300000000000)
      constant := (1633214452825146353839074302071197932746093991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132276934062552149927/50000000000000000000)
  centralHi := (52910773625020859971/20000000000000000000)
  directionLo := (16827287563137415663/6250000000000000000)
  directionHi := (269236601010198650609/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree030.table
  base := (-835027415823910155048700680794975424833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (4067294)
      previous := (2033647)
      next := (2033647)
      square := (30533688472578113783546805029098750000000000)
      linear := (-904223302027654809274555130842296912500000000)
      constant := (6451813984930928416190933237377539850852092007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree030.table
  base := (-6700583485931331996905924414676375489969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-27186182450654034983628169719647700000000000)
      constant := (194501056525522640285241356629398427091423759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16827287563137415663/6250000000000000000)
  centralHi := (269236601010198650609/100000000000000000000)
  directionLo := (136919634737950134899/50000000000000000000)
  directionHi := (273839269475900269799/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree031.table
  base := (-1364412738531452332867274397653297518249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-67274632119859983016803923746238972700000000000)
      constant := (496834837829054072029360297271678013276535202195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree031.table
  base := (-6840951301822382623919245212769092442433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-252833065321287517792970299135809300000000000)
      constant := (1872254605490809705673004387391263424971714167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136919634737950134899/50000000000000000000)
  centralHi := (273839269475900269799/100000000000000000000)
  directionLo := (139182922525237044073/50000000000000000000)
  directionHi := (278365845050474088147/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree032.table
  base := (-6924539638962870314640062643572742840987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-69445186493728819765839878071832567700000000000)
      constant := (530313523178735060448544057570278734993842541957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree032.table
  base := (-1388409385993902897891393748504194095511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-260990488586688720733287070794789300000000000)
      constant := (1998422121489293381853751033452929568349483445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139182922525237044073/50000000000000000000)
  centralHi := (278365845050474088147/100000000000000000000)
  directionLo := (282819981391404475093/100000000000000000000)
  directionHi := (141409990695702237547/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree033.table
  base := (-3495077598218215039196677225554975069091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (134456)
      previous := (67228)
      next := (67228)
      square := (1009378131324896323423034876995000000000000)
      linear := (-32881423722496628335572007528662150000000000)
      constant := (259393987714963207337910472613865954859112509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree033.table
  base := (-224203946747793616053482459045650837/320000000000000000000000000000000000)
  polynomial :=
    { denominator := 45000000000000000000000000000000000000000
      center := (504)
      previous := (252)
      next := (252)
      square := (3783591496011689675471600955000000000000)
      linear := (-123575717103806209216530689831850000000000)
      constant := (977496568025863283189445419455255351046875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282819981391404475093/100000000000000000000)
  centralHi := (141409990695702237547/50000000000000000000)
  directionLo := (143602524401387350529/50000000000000000000)
  directionHi := (287205048802774701059/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree034.table
  base := (-7021141444983856789780282269179864125709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-73786295241466493263911786723019757700000000000)
      constant := (600768750442330368263068332700223800799014060499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree034.table
  base := (-703615665246582206007475021449852393249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-138652667558745563306960307056374650000000000)
      constant := (1131964499087456629212483162261773083468832755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143602524401387350529/50000000000000000000)
  centralHi := (287205048802774701059/100000000000000000000)
  directionLo := (145762082038997732889/50000000000000000000)
  directionHi := (291524164077995465779/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree035.table
  base := (-1754871419207856629243226559157100841053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 133402500000000000000000000000000000000000000
      center := (1494108)
      previous := (747054)
      next := (747054)
      square := (11216456989926654042935561031097500000000000)
      linear := (-387534947017016989861978270656190575000000000)
      constant := (3253746237882820096660353529895770879520570867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree035.table
  base := (-7033379364567797942537690003299489649571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-285462758382892329554237385771729300000000000)
      constant := (2403227110199454264276905344554212201944554629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145762082038997732889/50000000000000000000)
  centralHi := (291524164077995465779/100000000000000000000)
  directionLo := (295780216419124026061/100000000000000000000)
  directionHi := (147890108209562013031/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree036.table
  base := (-6986960123159862669222402407285794967999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-8680822665467129640220410597134105300000000000)
      constant := (75094667550880364790982259840669846860101962521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree036.table
  base := (-3499904525621640846543032993895174671179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (50868285668601605636895968395000000000000)
      linear := (-1812470257088231682065149119942650000000000)
      constant := (15721386032046295708687846567524083864787341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295780216419124026061/100000000000000000000)
  centralHi := (147890108209562013031/50000000000000000000)
  directionLo := (37496986255671616281/12500000000000000000)
  directionHi := (299975890045372930249/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree037.table
  base := (-6925146917854785229803090889242148868143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-80297958363073003511019649699800542700000000000)
      constant := (715117849652934742954853924050494367418104047473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree037.table
  base := (-1734255840235956281430794809431720498987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-75444401228423683858717732272422325000000000)
      constant := (673706454154644130171874342223234482389428413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37496986255671616281/12500000000000000000)
  centralHi := (299975890045372930249/100000000000000000000)
  directionLo := (304113683993475529437/100000000000000000000)
  directionHi := (152056841996737764719/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree038.table
  base := (-683545985618393833952513064698655844853/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-41234256368470920130027802012697068850000000000)
      constant := (377764045537566147896839637290133653163385771415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree038.table
  base := (-1711607944489841206558903602495438627969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-77483757044773984593796925187167325000000000)
      constant := (711774283531289610859952425798578056007275831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304113683993475529437/100000000000000000000)
  centralHi := (152056841996737764719/50000000000000000000)
  directionLo := (154097964762398239969/50000000000000000000)
  directionHi := (308195929524796479939/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree039.table
  base := (-1679790853199205262048160470391188983877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (8134588)
      previous := (4067294)
      next := (4067294)
      square := (61067376945156227567093610058197500000000000)
      linear := (-2351085197522518805808098843082992575000000000)
      constant := (22141095167126642155952308469749871497715070083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree039.table
  base := (-6729294645287084598363965357512800763543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-35343605716055237923944941378627700000000000)
      constant := (333740681898836697178211842943353859968501673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154097964762398239969/50000000000000000000)
  centralHi := (308195929524796479939/100000000000000000000)
  directionLo := (312224805483521989159/100000000000000000000)
  directionHi := (7805620137088049729/2500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree040.table
  base := (-6577389407550910024876994509768569971537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-86809621484679513758127512676581327700000000000)
      constant := (839768895120283882602287863906312060549691893007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree040.table
  base := (-6586739832978052997747085147507112716403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-326249874709898344255821244066629300000000000)
      constant := (3164521771257321491265971619869054788266534197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312224805483521989159/100000000000000000000)
  centralHi := (7805620137088049729/2500000000000000000)
  directionLo := (39525293986650372653/12500000000000000000)
  directionHi := (12648094075728119249/4000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree041.table
  base := (-1282230329117867437115794193293716583923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-88980175858548350507163467002174922700000000000)
      constant := (883593847601150700311377381742368038094494775265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree041.table
  base := (-3209888689420003547641015762874480332153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-167203648987649773598069007862804650000000000)
      constant := (1664827068623989231197071370182245368264568447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39525293986650372653/12500000000000000000)
  centralHi := (12648094075728119249/4000000000000000000)
  directionLo := (320130482032503101559/100000000000000000000)
  directionHi := (8003262050812577539/2500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree042.table
  base := (-6221358807034511555205774870212727121239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (664048)
      previous := (332024)
      next := (332024)
      square := (4985091995522957352415804902710000000000000)
      linear := (-206690998259449404209068982602649700000000000)
      constant := (2105559881050428546962870900446679890898173969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree042.table
  base := (-6229312377226016949650415942746146353981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-38062746804522305570717198598287700000000000)
      constant := (388783818247971860927031274905562846620514691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320130482032503101559/100000000000000000000)
  centralHi := (8003262050812577539/2500000000000000000)
  directionLo := (8100274829825706881/2500000000000000000)
  directionHi := (324010993193028275241/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree043.table
  base := (-3004412909735419900478759777259528716267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-46660642303143012002617687826681056350000000000)
      constant := (487320472082179002307889561419131226295392554037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree043.table
  base := (-6016156349376852951962915615250710084221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-350722144506101953076771559043569300000000000)
      constant := (3672714498488945558510112073824392690464549979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8100274829825706881/2500000000000000000)
  centralHi := (324010993193028275241/100000000000000000000)
  directionLo := (327845576290884912539/100000000000000000000)
  directionHi := (16392278814544245627/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree044.table
  base := (-5774283911384700151463766170779233559403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (2420208)
      previous := (1210104)
      next := (1210104)
      square := (18168806363848133821614627785910000000000000)
      linear := (-789188751902106287225382892388063700000000000)
      constant := (8445116078755602700186771490486171842014860573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree044.table
  base := (-5781037293724427248507529323288605558567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9072)
      previous := (4536)
      next := (4536)
      square := (68104646928210414158488817190000000000000)
      linear := (-2965946841086802942289986204153300000000000)
      constant := (31823366982702014230982362506978822949756073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327845576290884912539/100000000000000000000)
  centralHi := (16392278814544245627/5000000000000000000)
  directionLo := (66327164895560631421/20000000000000000000)
  directionHi := (165817912238901578553/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree045.table
  base := (-2759194757788987646395852668417740827151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-5425688519667983194628182461363850150000000000)
      constant := (59455805292823468538474245169961310017155264329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree045.table
  base := (-345288036585536875169377759066503371303/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12717071417150401409223992098750000000000)
      linear := (-566415109624852405798464664138162500000000)
      constant := (6223436234191956183962664665982593684144674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66327164895560631421/20000000000000000000)
  centralHi := (165817912238901578553/50000000000000000000)
  directionLo := (335383240876228172683/100000000000000000000)
  directionHi := (83845810219057043171/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree046.table
  base := (-2620866083603549311887274605332987532063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-49916473863946267126171619315071448850000000000)
      constant := (559837875968726442919214249152780511387777726593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree046.table
  base := (-4197965495633185906936700741290678829/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-187597207151152780948860937010254650000000000)
      constant := (2109593286663678499344290709377120185498106875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335383240876228172683/100000000000000000000)
  centralHi := (83845810219057043171/25000000000000000000)
  directionLo := (169544622772451789729/50000000000000000000)
  directionHi := (339089245544903579459/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree047.table
  base := (-4944841520665361770470207332571470191079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-102003502101761371001379192955736492700000000000)
      constant := (1170271430647803341871829876649579675827557840569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree047.table
  base := (-4950109073412961336943619303177985592909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-383351837567706764838038645679489300000000000)
      constant := (4409821921206660128467819227916994663203898891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169544622772451789729/50000000000000000000)
  centralHi := (339089245544903579459/100000000000000000000)
  directionLo := (85688795441623279429/25000000000000000000)
  directionHi := (342755181766493117717/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree048.table
  base := (-4628193592329018085451124311217636840801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-11574895163958911972268349697925565300000000000)
      constant := (135776698529676776921172917274441345327373652679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree048.table
  base := (-463303864337236174828622075434560575487/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (60984)
      previous := (30492)
      next := (30492)
      square := (457814571017414450732063715555000000000000)
      linear := (-21750514490728220432130856518803850000000000)
      constant := (255816004619235284740567027644363617666473285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85688795441623279429/25000000000000000000)
  centralHi := (342755181766493117717/100000000000000000000)
  directionLo := (21648895108511705121/6250000000000000000)
  directionHi := (346382321736187281937/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree049.table
  base := (-4292216321664940093414778847694268922749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-44291799604122884006435277637202700000000000)
      constant := (530958434555060033169462269420768241143126339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree049.table
  base := (-214833555019105436609465931149302432041/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-99916671024627292679668047249362325000000000)
      constant := (1200945222153782315182155120350106109317830795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/6250000000000000000)
  centralHi := (346382321736187281937/100000000000000000000)
  directionLo := (87492967929900437989/25000000000000000000)
  directionHi := (349971871719601751957/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree050.table
  base := (-1968647265445611489263956321840104927109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-54257582611683940624243527966258638850000000000)
      constant := (664396584128103587420402041592118019763242295899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree050.table
  base := (-1970694496839187999560924777442796163317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-203912053681955186829494480328214650000000000)
      constant := (2503548294124139398063377565628640654803330083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87492967929900437989/25000000000000000000)
  centralHi := (349971871719601751957/100000000000000000000)
  directionLo := (176762488369627796933/50000000000000000000)
  directionHi := (353524976739255593867/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree051.table
  base := (-3563774352918207707590790687342263802969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-12298413288581857555280334473123430300000000000)
      constant := (153763920267300210153465528924804634727697643151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree051.table
  base := (-1783768161309191603939412164988213707783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (60984)
      previous := (30492)
      next := (30492)
      square := (457814571017414450732063715555000000000000)
      linear := (-23110085034961754255516985128633850000000000)
      constant := (289701767250443534536042252584166685272224313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176762488369627796933/50000000000000000000)
  centralHi := (353524976739255593867/100000000000000000000)
  directionLo := (178521362420622530437/50000000000000000000)
  directionHi := (2856341798729960487/800000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree052.table
  base := (-3171967188369803275338534300552148889953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-112856273971105554746558964583704467700000000000)
      constant := (1440076729599397361275500960662318125271077680383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree052.table
  base := (-3175422487536365134152287738040340099537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-424138953894712779539622503974389300000000000)
      constant := (5426383522961567902258078996188930226684437863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178521362420622530437/50000000000000000000)
  centralHi := (2856341798729960487/800000000000000000)
  directionLo := (360526150987179925893/100000000000000000000)
  directionHi := (180263075493589962947/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree053.table
  base := (-2762153244842498238765307883297134152219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-115026828344974391495594918909298062700000000000)
      constant := (1497396777181573329455139169480626965200668655109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree053.table
  base := (-553065164563823627149062943765328015849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-432296377160113982479939275633369300000000000)
      constant := (5642348997653706646851882542794588000583319755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360526150987179925893/100000000000000000000)
  centralHi := (180263075493589962947/50000000000000000000)
  directionLo := (181988120305420403853/50000000000000000000)
  directionHi := (363976240610840807707/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree054.table
  base := (-1167292352497692951755035827515522655053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-6510965706602401569146159624160647650000000000)
      constant := (86435264765166948550215364417829151567731347387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree054.table
  base := (-1168748379420188671829614099949515295921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (50868285668601605636895968395000000000000)
      linear := (-2718850619910587564322568193162650000000000)
      constant := (36188430741458684428464365557524208649193559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181988120305420403853/50000000000000000000)
  centralHi := (363976240610840807707/100000000000000000000)
  directionLo := (367393932874197727139/100000000000000000000)
  directionHi := (18369696643709886357/5000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree055.table
  base := (-944744282204205150499389487424149692349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 108045000000000000000000000000000000000000000
      center := (1210104)
      previous := (605052)
      next := (605052)
      square := (9084403181924066910807313892955000000000000)
      linear := (-493255938399636632205234824630104350000000000)
      constant := (6675165710127465563397223290168075174298030459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree055.table
  base := (-1892160653730431968038582573038244422319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9072)
      previous := (4536)
      next := (4536)
      square := (68104646928210414158488817190000000000000)
      linear := (-3707530774305094118682419991333300000000000)
      constant := (50305055054663914292458564059240402201792161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367393932874197727139/100000000000000000000)
  centralHi := (18369696643709886357/5000000000000000000)
  directionLo := (370780123653278277473/100000000000000000000)
  directionHi := (185390061826639138737/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree056.table
  base := (-1427069175256888139836250776473323809847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5976432)
      previous := (2988216)
      next := (2988216)
      square := (44865827959706616171742244124390000000000000)
      linear := (-2480377376868997994749036365022017300000000000)
      constant := (34205352063218636328579354468112170768182754233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree056.table
  base := (-142952033106222576965032635245950576837/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-228384323478158795650444795305154650000000000)
      constant := (3157752327136974240490691386477132591982102815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370780123653278277473/100000000000000000000)
  centralHi := (185390061826639138737/50000000000000000000)
  directionLo := (23383479267549109491/6250000000000000000)
  directionHi := (374135668280785751857/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree057.table
  base := (-947510527611261217200562800593384100029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-13745449537827748721304304023519160300000000000)
      constant := (193094525826310146865159534665672156557875474891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree057.table
  base := (-474879177645351775206486662235706040267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (60984)
      previous := (30492)
      next := (30492)
      square := (457814571017414450732063715555000000000000)
      linear := (-25829226123428821902289242348293850000000000)
      constant := (363794609376718251010517412892102266122149237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23383479267549109491/6250000000000000000)
  centralHi := (374135668280785751857/100000000000000000000)
  directionLo := (188730692034629053551/50000000000000000000)
  directionHi := (377461384069258107103/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree058.table
  base := (-450978296484753381073136392149202247469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-125879600214318575240774690537266037700000000000)
      constant := (1800755112679446440150415670786351604874767527859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree058.table
  base := (-226519536545525271753569606475857307223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-236541746743559998590761566964134650000000000)
      constant := (3392652497186755125270437506884544822531907377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188730692034629053551/50000000000000000000)
  centralHi := (377461384069258107103/100000000000000000000)
  directionLo := (380758052635856674797/100000000000000000000)
  directionHi := (190379026317928337399/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree059.table
  base := (62378320462955522497813559109406718619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-128050154588187411989810644862859632700000000000)
      constant := (1864775001720198944555343984381537901093699194491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree059.table
  base := (12097910895485033674751320732735458469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-481240916752521200121839905587249300000000000)
      constant := (7026509280885351399517589314759961401142273345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380758052635856674797/100000000000000000000)
  centralHi := (190379026317928337399/50000000000000000000)
  directionLo := (76805284409503914361/20000000000000000000)
  directionHi := (192013211023759785903/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree060.table
  base := (592424952468624800579835147386804458239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-14468967662450694304316288798717025300000000000)
      constant := (214434449802365807550784210337277267318012052519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree060.table
  base := (147673576717398593951450951173220315373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (30492)
      previous := (15246)
      next := (15246)
      square := (228907285508707225366031857777500000000000)
      linear := (-13594398333831177862837685479061925000000000)
      constant := (201997625628385809826052571943818136923441197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76805284409503914361/20000000000000000000)
  centralHi := (192013211023759785903/50000000000000000000)
  directionLo := (387267208803158869317/100000000000000000000)
  directionHi := (193633604401579434659/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree061.table
  base := (284760143205322835353698308246009300187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (549606392506406048103842490523777500000000000)
      linear := (-33097815833981271371970638378511705675000000000)
      constant := (499039983933879137231959407534484950361096646843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree061.table
  base := (284363806592516360171500680482404082693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-124388940820830901500618362226302325000000000)
      constant := (1880379885969388739939184334918368617414474093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387267208803158869317/100000000000000000000)
  centralHi := (193633604401579434659/50000000000000000000)
  directionLo := (195240549833890343547/50000000000000000000)
  directionHi := (78096219933556137419/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree062.table
  base := (1702116166162259923795639861273403320329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-134561817709793922236918507839640417700000000000)
      constant := (2063524379221612576018440560679433537304227712681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree062.table
  base := (1700664290348974381887397060321437382691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-505713186548724808942790220564189300000000000)
      constant := (7775323285922553520695098265200217007787754491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195240549833890343547/50000000000000000000)
  centralHi := (78096219933556137419/20000000000000000000)
  directionLo := (39366875337182794853/10000000000000000000)
  directionHi := (393668753371827948531/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree063.table
  base := (45631070607337000268706426807705651769/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (332024)
      previous := (166012)
      next := (166012)
      square := (2492545997761478676207902451355000000000000)
      linear := (-155025365174220815176819118101172350000000000)
      constant := (2417237099672976383681805218287342095233460025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree063.table
  base := (2280224217890081698802726692259478654633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (101736571337203211273791936790000000000000)
      linear := (-6344081602643531010902555459545300000000000)
      constant := (99176849324773145348241032222802296917210593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39366875337182794853/10000000000000000000)
  centralHi := (393668753371827948531/100000000000000000000)
  directionLo := (396830802187656449781/100000000000000000000)
  directionHi := (198415401093828224891/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree064.table
  base := (2877264199127804268235532715716865006979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-138902926457531595734990416490827607700000000000)
      constant := (2201595932493493875702018880804500906848232914531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree064.table
  base := (359505924613490156840504949956611977891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (137214)
      previous := (68607)
      next := (68607)
      square := (1030082784789182514147143359998750000000000)
      linear := (-65253504134940901852927970485268662500000000)
      constant := (1036940401667964882961017342060559153995309691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396830802187656449781/100000000000000000000)
  centralHi := (198415401093828224891/50000000000000000000)
  directionLo := (12498995418557205427/3125000000000000000)
  directionHi := (79993570678766114733/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree065.table
  base := (3489168472847678404559629774067425516967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-141073480831400432484026370816421202700000000000)
      constant := (2272302602577737949905902981883459483257532928263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree065.table
  base := (3488054919360220362096136663667420076983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-530185456344928417763740535541129300000000000)
      constant := (8561917766656114077526215137948983884174510383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/3125000000000000000)
  centralHi := (79993570678766114733/20000000000000000000)
  directionLo := (25192530664802725793/6250000000000000000)
  directionHi := (403080490636843612689/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree066.table
  base := (4117194546764986785840803393557921399807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (268912)
      previous := (134456)
      next := (134456)
      square := (2018756262649792646846069753990000000000000)
      linear := (-131537222410715582399506267348039300000000000)
      constant := (2152546321778858942976506218723815119280936607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree066.table
  base := (257260982092564949323978814942944522337/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11250000000000000000000000000000000000000
      center := (126)
      previous := (63)
      next := (63)
      square := (945897874002922418867900238750000000000)
      linear := (-61793259826713684653817413590462500000000)
      constant := (1013832387358750211022832252295748001402066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25192530664802725793/6250000000000000000)
  centralHi := (403080490636843612689/100000000000000000000)
  directionLo := (203084637599455313583/50000000000000000000)
  directionHi := (406169275198910627167/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree067.table
  base := (4761277726407715899828271896233631925301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-145414589579138105982098279467608392700000000000)
      constant := (2417056788855887858150222267630076700975133346389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree067.table
  base := (297521610195651793204584663683134512247/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (137214)
      previous := (68607)
      next := (68607)
      square := (1030082784789182514147143359998750000000000)
      linear := (-68312537859466352955546759857386162500000000)
      constant := (1138411570245185588226875303241582815209065694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203084637599455313583/50000000000000000000)
  centralHi := (406169275198910627167/100000000000000000000)
  directionLo := (81846949435926619553/20000000000000000000)
  directionHi := (204617373589816548883/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree068.table
  base := (1355339930376593366650441562657375983167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (549606392506406048103842490523777500000000000)
      linear := (-36896285988251735682783558448300496925000000000)
      constant := (622775995870735727288107879972343315777050940063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree068.table
  base := (1084101481079247501655984332360360772721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-554657726141132026584690850518069300000000000)
      constant := (9386271611378070684198282686183891879667192605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81846949435926619553/20000000000000000000)
  centralHi := (204617373589816548883/50000000000000000000)
  directionLo := (206138713299290317851/50000000000000000000)
  directionHi := (412277426598580635703/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree069.table
  base := (6097388010422815705843012837299800927207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-16639522036319531053352243124310620300000000000)
      constant := (285140487885621447265025158048485488665173104847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree069.table
  base := (6096608698508833622507814982601400460991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-62535016600725914391667513575227700000000000)
      constant := (1074382710870878401130591256088119225102019199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206138713299290317851/50000000000000000000)
  centralHi := (412277426598580635703/100000000000000000000)
  directionLo := (415297814425163894353/100000000000000000000)
  directionHi := (207648907212581947177/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree070.table
  base := (6789315267974350378101584214617142437109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5976432)
      previous := (2988216)
      next := (2988216)
      square := (44865827959706616171742244124390000000000000)
      linear := (-3100535769402951351616451886620187300000000000)
      constant := (53929344644453134662443481154982527587586573349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree070.table
  base := (6788602852953628673120047105016379502143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-570972572671934432465324393836029300000000000)
      constant := (9956810462756957003221554967504866535500503543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415297814425163894353/100000000000000000000)
  centralHi := (207648907212581947177/50000000000000000000)
  directionLo := (83659278708314881619/20000000000000000000)
  directionHi := (13071762298174200253/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree071.table
  base := (7497098850266895240702863131785283565299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-154096807074613452978242096769982772700000000000)
      constant := (2719924361805253854370927330057829441750068077011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree071.table
  base := (7496447719401268786911904951836792976049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-579129995937335635405641165495009300000000000)
      constant := (10248369393029647866025704281449537707958256249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83659278708314881619/20000000000000000000)
  centralHi := (13071762298174200253/3125000000000000000)
  directionLo := (8425472592880651377/2000000000000000000)
  directionHi := (421273629644032568851/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree072.table
  base := (8220700330806583812448402045743573734639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-17363040160942476636364227899508485300000000000)
      constant := (310935968130934774651439821691056495384961056919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree072.table
  base := (2055026331932877048884399807998544689011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25434142834300802818447984197500000000000)
      linear := (-1812615491366471723289993633191325000000000)
      constant := (32543582767008733548803123968473223907370331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8425472592880651377/2000000000000000000)
  centralHi := (421273629644032568851/100000000000000000000)
  directionLo := (1325718662772208477/312500000000000000)
  directionHi := (424229972087106712641/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree073.table
  base := (8960085082745138932183804151769835442683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-158437915822351126476314005421169962700000000000)
      constant := (2878035851159241655973602143452238676363793370587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree073.table
  base := (4479770736006557469282162861353458730359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-297722421234069020643137354406484650000000000)
      constant := (5422032198974085205068438353162372199016248559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1325718662772208477/312500000000000000)
  centralHi := (424229972087106712641/100000000000000000000)
  directionLo := (42716585467543770511/10000000000000000000)
  directionHi := (427165854675437705111/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree074.table
  base := (4857610951319218863639297120016844285117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-80304235098109981612674979873381778850000000000)
      constant := (1479380347080218898256571635080051954342008283613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree074.table
  base := (2428681334206636645840476117982973616823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-150900566433384811056647870117987325000000000)
      constant := (2787049958829935787904372377339455674418482223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42716585467543770511/10000000000000000000)
  centralHi := (427165854675437705111/100000000000000000000)
  directionLo := (53760212050852340377/12500000000000000000)
  directionHi := (430081696406818723017/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree075.table
  base := (5243041335783429231809447574696741339693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-9043279142782711109688106337353175150000000000)
      constant := (168922120481098420369401849776806436365748950053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree075.table
  base := (838850332862838623581192092495732907/800000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (30492)
      previous := (15246)
      next := (15246)
      square := (228907285508707225366031857777500000000000)
      linear := (-16993324694415012421303007003636925000000000)
      constant := (318236857126005571351363726474450166049134375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53760212050852340377/12500000000000000000)
  centralHi := (430081696406818723017/100000000000000000000)
  directionLo := (21648895108511705121/5000000000000000000)
  directionHi := (432977902170234102421/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree076.table
  base := (11272642049886284311667381352333504919177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-164949578943957636723421868397950747700000000000)
      constant := (3123548208401954230192966100773259982343617990953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree076.table
  base := (563611396676683946646731248099806954587/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-154979278066085412526806255947477325000000000)
      constant := (2942261304117760276879157907207182739809535935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21648895108511705121/5000000000000000000)
  centralHi := (432977902170234102421/100000000000000000000)
  directionLo := (87170972680429954517/20000000000000000000)
  directionHi := (217927431701074886293/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree077.table
  base := (6037438601127686593464068355642617988527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (24696)
      previous := (12348)
      next := (12348)
      square := (185395983304572794098108446795000000000000)
      linear := (-14093450271363338967149420030658150000000000)
      constant := (270501834515067462367243476308189694532940407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree077.table
  base := (12074499122870355422058469352400009408971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9072)
      previous := (4536)
      next := (4536)
      square := (68104646928210414158488817190000000000000)
      linear := (-5190698640741676471467287565693300000000000)
      constant := (99882270200712106839649277520123500762126651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87170972680429954517/20000000000000000000)
  centralHi := (217927431701074886293/50000000000000000000)
  directionLo := (438712958704067073523/100000000000000000000)
  directionHi := (109678239676016768381/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree078.table
  base := (3223191887480648023901224653016891071349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (8134588)
      previous := (4067294)
      next := (4067294)
      square := (61067376945156227567093610058197500000000000)
      linear := (-4702519102547091950597049362476053825000000000)
      constant := (91466270852385653201962173993107375123439382829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree078.table
  base := (12892422428995178696305422135748216505171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-70692439866127117331984285234207700000000000)
      constant := (1378517232335914328845908583989820407774131219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438712958704067073523/100000000000000000000)
  centralHi := (109678239676016768381/25000000000000000000)
  directionLo := (3449629331438267919/781250000000000000)
  directionHi := (441552554424098293633/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree079.table
  base := (1715786818444964963435598313728010194991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (274803196253203024051921245261888750000000000)
      linear := (-21432655258195518371316216421841441587500000000)
      constant := (422384143866291146006361059927795780629980822799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree079.table
  base := (13725979563166992479711688493832676614791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-644389382060545258928175338766849300000000000)
      constant := (12731746227434281130902754503735793763501566591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3449629331438267919/781250000000000000)
  centralHi := (441552554424098293633/100000000000000000000)
  directionLo := (444374005205093100251/100000000000000000000)
  directionHi := (111093501301273275063/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree080.table
  base := (14575441482200727943867845650697458993453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-173631796439432983719565685700325127700000000000)
      constant := (3466472910713798496100455883078607154358132631117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree080.table
  base := (1457515404834251815144024752735572156821/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-326273402662973230934246055212914650000000000)
      constant := (6530513971013910133851735340791578713545013105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444374005205093100251/100000000000000000000)
  centralHi := (111093501301273275063/25000000000000000000)
  directionLo := (447177654501637563577/100000000000000000000)
  directionHi := (223588827250818781789/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree081.table
  base := (308803865841788649139030413447306768027/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-9766797267405656692700091112551040150000000000)
      constant := (197499166147471293529064942169046274888849301675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree081.table
  base := (15439931039605538591361312537020378906957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13552)
      previous := (6776)
      next := (6776)
      square := (101736571337203211273791936790000000000000)
      linear := (-8156842328288242775417393605985300000000000)
      constant := (165364198633442253407665848765563765847741797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447177654501637563577/100000000000000000000)
  centralHi := (223588827250818781789/50000000000000000000)
  directionLo := (112490958767014848843/25000000000000000000)
  directionHi := (449963835068059395373/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree082.table
  base := (16320536403458958943574271929072177822061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-177972905187170657217637594351512317700000000000)
      constant := (3644609355261204595514168564380222713707386854029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree082.table
  base := (408007429060413113249368815080337752787/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (137214)
      previous := (68607)
      next := (68607)
      square := (1030082784789182514147143359998750000000000)
      linear := (-83607706482093608468640706717973662500000000)
      constant := (1716520317274178247435596615734398526575326935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112490958767014848843/25000000000000000000)
  centralHi := (449963835068059395373/100000000000000000000)
  directionLo := (452732869419402308849/100000000000000000000)
  directionHi := (9054657388388046177/2000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree083.table
  base := (1076028661466468318008773973580775569609/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (274803196253203024051921245261888750000000000)
      linear := (-22517932445129936745834193584638239087500000000)
      constant := (466918246568609380335803006553448053405400773202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree083.table
  base := (17216240366909848330298072527485608325647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-677019075122150070689442425402769300000000000)
      constant := (14074015170580897611624922773736723347199666247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452732869419402308849/100000000000000000000)
  centralHi := (9054657388388046177/2000000000000000000)
  directionLo := (18219402810687090419/4000000000000000000)
  directionHi := (113871267566794315119/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree084.table
  base := (9063974403830135199433105035536718143779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (332024)
      previous := (166012)
      next := (166012)
      square := (2492545997761478676207902451355000000000000)
      linear := (-206705231218716928249103744901019850000000000)
      constant := (4339223144775516323802356161900245851874465691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree084.table
  base := (141623045286273178083371745269041675153/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (15246)
      previous := (7623)
      next := (7623)
      square := (114453642754353612683015928888750000000000)
      linear := (-9516340255382656578191099959190962500000000)
      constant := (200278581667600611896682231701881132147865872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18219402810687090419/4000000000000000000)
  centralHi := (113871267566794315119/25000000000000000000)
  directionLo := (114555185232889292003/25000000000000000000)
  directionHi := (458220740931557168013/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree085.table
  base := (152439977124794986014884493128558189373/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-184484568308777167464745457328293102700000000000)
      constant := (3920155852712484050573836380398699777451687499625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree085.table
  base := (3810963134072260376393594329219027571389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-693333921652952476570075968720729300000000000)
      constant := (14770290570786389194912277852089643946135917945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114555185232889292003/25000000000000000000)
  centralHi := (458220740931557168013/100000000000000000000)
  directionLo := (460940175731553101511/100000000000000000000)
  directionHi := (57617521966444137689/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree086.table
  base := (1999759462822247098267150786930968416813/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-93327561341323002106890705826943348850000000000)
      constant := (2007114533099116589540096817871498566118941830785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree086.table
  base := (9998714587742922626549978126828789063033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-350745672459176839755196370189854650000000000)
      constant := (7562356578183123082973499920518023861606786433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460940175731553101511/100000000000000000000)
  centralHi := (57617521966444137689/12500000000000000000)
  directionLo := (23182183017729633079/5000000000000000000)
  directionHi := (463643660354592661581/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree087.table
  base := (4191146640180160961770799000491806750393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-20980630784057204551424151775497810300000000000)
      constant := (456601603672187025937848602852850825794654623765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree087.table
  base := (20955582372159402882614333177936989972509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-78849863131528320272301056893187700000000000)
      constant := (1720369506554252734557979977398508282080062301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23182183017729633079/5000000000000000000)
  centralHi := (463643660354592661581/100000000000000000000)
  directionLo := (233165736103407088459/50000000000000000000)
  directionHi := (466331472206814176919/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree088.table
  base := (1096470279302947484725353110401382032787/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54022500000000000000000000000000000000000000
      center := (605052)
      previous := (302526)
      next := (302526)
      square := (4542201590962033455403656946477500000000000)
      linear := (-394620312872693548991432479969160925000000000)
      constant := (8689487467461386876329489468633342471732471415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree088.table
  base := (21929268106803349598173141688675842779149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9072)
      previous := (4536)
      next := (4536)
      square := (68104646928210414158488817190000000000000)
      linear := (-5932282573959967647859721352873300000000000)
      constant := (130959733128431821692749201368793143265111069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233165736103407088459/50000000000000000000)
  centralHi := (466331472206814176919/100000000000000000000)
  directionLo := (234501940372646238431/50000000000000000000)
  directionHi := (469003880745292476863/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree089.table
  base := (2291860522943549322735878028999114990941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-96583392902126257230444637315333741350000000000)
      constant := (2151560776332881002514934594447007190032742661745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree089.table
  base := (11459239967120548073386819962486082931277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-362981807357278644165671527678324650000000000)
      constant := (8106559770926498928040410337584767448809445877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234501940372646238431/50000000000000000000)
  centralHi := (469003880745292476863/100000000000000000000)
  directionLo := (471661147793322437757/100000000000000000000)
  directionHi := (235830573896661218879/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree090.table
  base := (747603944503935426056406652164095576619/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (4067294)
      previous := (2033647)
      next := (2033647)
      square := (30533688472578113783546805029098750000000000)
      linear := (-2713018613585018766804517068836959412500000000)
      constant := (61133934345115517767526431363293869687809713996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree090.table
  base := (5980803011884590455888538539432128026899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (3388)
      previous := (1694)
      next := (1694)
      square := (25434142834300802818447984197500000000000)
      linear := (-2265805672777649664418703169801325000000000)
      constant := (51186114203743067961753001422853037491254779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471661147793322437757/100000000000000000000)
  centralHi := (235830573896661218879/50000000000000000000)
  directionLo := (474303527839804471837/100000000000000000000)
  directionHi := (237151763919902235919/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree091.table
  base := (6235890811659467449203888987754663756639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 133402500000000000000000000000000000000000000
      center := (1494108)
      previous := (747054)
      next := (747054)
      square := (11216456989926654042935561031097500000000000)
      linear := (-1007693339550970346729393792254360575000000000)
      constant := (22965699392243367592118815936505308000218013679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree091.table
  base := (997738368591794006578904683715457909317/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-742278461245359694211976598674609300000000000)
      constant := (16959672037741664109760032421579451374230397925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474303527839804471837/100000000000000000000)
  centralHi := (237151763919902235919/50000000000000000000)
  directionLo := (95386253664740183011/20000000000000000000)
  directionHi := (29808204270231307191/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree092.table
  base := (2597931149926488144392257419774276152573/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-99839224462929512353998568803724133850000000000)
      constant := (2301011482107700054547112566588376639645474723985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree092.table
  base := (5195843344439598195451749215164817878939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-750435884510760897152293370333589300000000000)
      constant := (17339232602839651126082559516596787500157405695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95386253664740183011/20000000000000000000)
  centralHi := (29808204270231307191/6250000000000000000)
  directionLo := (239772304952231620333/50000000000000000000)
  directionHi := (479544609904463240667/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree093.table
  base := (5406113331630845268788109276289516490881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-22427667033303095717448121325893540300000000000)
      constant := (522653434616654139960777605300915838502236195005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree093.table
  base := (5406096064543577795644819047053629344867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-84288145308462455565845571332507700000000000)
      constant := (1969220295075730562766680365341338111782800815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239772304952231620333/50000000000000000000)
  centralHi := (479544609904463240667/100000000000000000000)
  directionLo := (482143786719266608649/100000000000000000000)
  directionHi := (9642875734385332173/2000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree094.table
  base := (878041400828292982425649716992944399337/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (36605646)
      previous := (18302823)
      next := (18302823)
      square := (274803196253203024051921245261888750000000000)
      linear := (-25502444709199587275758630782329432212500000000)
      constant := (600856364086780002648526248901795537950482244772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree094.table
  base := (28097246189884270411571360591189304430453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-766750731041563303032926913651549300000000000)
      constant := (18110922158764200773132154359696950572722869853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482143786719266608649/100000000000000000000)
  centralHi := (9642875734385332173/2000000000000000000)
  directionLo := (484729026627829945521/100000000000000000000)
  directionHi := (242364513313914972761/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree095.table
  base := (29179582492392150764480795497466085927971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-206190112047465534955105000584229052700000000000)
      constant := (4910932958465863647392543703863795002998920566019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree095.table
  base := (29179510876141729316715474633487153002373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-774908154306964505973243685310529300000000000)
      constant := (18503051078298037716958958484805016086576257773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484729026627829945521/100000000000000000000)
  centralHi := (242364513313914972761/50000000000000000000)
  directionLo := (243650275722773037323/50000000000000000000)
  directionHi := (487300551445546074647/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree096.table
  base := (605546729815028795828062701466649094033/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-11575592578963020650230053050545702650000000000)
      constant := (278673724477172357422994184382292573436189029825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree096.table
  base := (1211090851013182398895025052499886799427/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-87007286396929523212617828552167700000000000)
      constant := (2099929931537733868845140270477608618114400075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243650275722773037323/50000000000000000000)
  centralHi := (487300551445546074647/100000000000000000000)
  directionLo := (244929288582798484759/50000000000000000000)
  directionHi := (489858577165596969519/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree097.table
  base := (31390583969126686010366539632300986834889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-210531220795203208453176909235416242700000000000)
      constant := (5122433151605669598572863209729586241866329084521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree097.table
  base := (31390524588877474472821892807182431641857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-791223000837766911853877228628489300000000000)
      constant := (19299877047960114689310007234608352112521840457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244929288582798484759/50000000000000000000)
  centralHi := (489858577165596969519/100000000000000000000)
  directionLo := (492403314170683608417/100000000000000000000)
  directionHi := (246201657085341804209/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree098.table
  base := (3251932235679509636836058978367987936059/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (60984)
      previous := (30492)
      next := (30492)
      square := (457814571017414450732063715555000000000000)
      linear := (-44294413821131204748482478875678850000000000)
      constant := (1089098559932095904461571140346215369311841255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree098.table
  base := (32519268295349041437168475169300869659223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-799380424103168114794194000287469300000000000)
      constant := (19704574045946968862106131170242919223530044623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492403314170683608417/100000000000000000000)
  centralHi := (246201657085341804209/50000000000000000000)
  directionLo := (494934967434957831413/100000000000000000000)
  directionHi := (247467483717478915707/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree099.table
  base := (2103971833559013005756206050356128393607/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3001250000000000000000000000000000000000000
      center := (33614)
      previous := (16807)
      next := (16807)
      square := (252344532831224080855758719248750000000000)
      linear := (-24663949672054738515983564954844287500000000)
      constant := (612761872600565102857263449145448497296100814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree099.table
  base := (16831750061500595206042023820324719034809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (56)
      previous := (28)
      next := (28)
      square := (420399055112409963941288995000000000000)
      linear := (-41196706834433696446000957654650000000000)
      constant := (1026092253623855397637054071903174719034809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494934967434957831413/100000000000000000000)
  centralHi := (247467483717478915707/50000000000000000000)
  directionLo := (248726868358352367829/50000000000000000000)
  directionHi := (497453736716704735659/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree100.table
  base := (17411631410798261366698549716243818771429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-108521441958404859350142386106098513850000000000)
      constant := (2724011797026426864868459505883379375509648920581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree100.table
  base := (6964643605012201698247198682601135678803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-815695270633970520674827543605429300000000000)
      constant := (20526535956663227297041249498880298653939741015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248726868358352367829/50000000000000000000)
  centralHi := (497453736716704735659/100000000000000000000)
  directionLo := (12498995418557205427/2500000000000000000)
  directionHi := (499959816742288217081/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree101.table
  base := (35998460929010705427679619148833126003621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-219213438290678555449320726537790622700000000000)
      constant := (5558777759743947825042065027191790222597281788869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree101.table
  base := (35998420157450672532152216466115502909553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-823852693899371723615144315264409300000000000)
      constant := (20943800831258403495165908901451212344016528953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12498995418557205427/2500000000000000000)
  centralHi := (499959816742288217081/100000000000000000000)
  directionLo := (502453397381839026993/100000000000000000000)
  directionHi := (251226698690919513497/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree102.table
  base := (7437828392662937570729825790976793977599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-24598221407171932466484075651487135300000000000)
      constant := (630071547415025268840107953635414387665830195395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree102.table
  base := (9297276214679509329072431801711261637187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (30492)
      previous := (15246)
      next := (15246)
      square := (228907285508707225366031857777500000000000)
      linear := (-23111392143465914626540585747871925000000000)
      constant := (593479304528790267321349230115457413922896643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502453397381839026993/100000000000000000000)
  centralHi := (251226698690919513497/50000000000000000000)
  directionLo := (504934663817133934903/100000000000000000000)
  directionHi := (63116832977141741863/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree103.table
  base := (19197652198075098547008951274720834704257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-111777273519208114473696317594488906350000000000)
      constant := (2891811045515255474518904275276411072997039031073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree103.table
  base := (19197635315977214847740196296530952723031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-420083770215087064747888929291184650000000000)
      constant := (10895449168663081888362021887525061317638426831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504934663817133934903/100000000000000000000)
  centralHi := (63116832977141741863/12500000000000000000)
  directionLo := (3964092161735047417/781250000000000000)
  directionHi := (507403796702086069377/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree104.table
  base := (9904236712532505791964597801756323987767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (549606392506406048103842490523777500000000000)
      linear := (-56431275353071266424107147378642851925000000000)
      constant := (1474428062257089806698688614811147297461250509463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree104.table
  base := (39616916128502844537681386919257424554509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-848324963695575332436094630241349300000000000)
      constant := (22220730940909358647333171639392489218058742709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3964092161735047417/781250000000000000)
  centralHi := (507403796702086069377/100000000000000000000)
  directionLo := (50986097231624006123/10000000000000000000)
  directionHi := (509860972316240061231/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree105.table
  base := (20427034041964486391995267742819772145123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (332024)
      previous := (166012)
      next := (166012)
      square := (2492545997761478676207902451355000000000000)
      linear := (-258385097263213041321388371700867350000000000)
      constant := (6817363262452486308968806134185600179048434267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree105.table
  base := (8170808026655847428896699088701027578589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-95164709662330726152934600211147700000000000)
      constant := (2517194751319666168145205240388660595165417105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50986097231624006123/10000000000000000000)
  centralHi := (509860972316240061231/100000000000000000000)
  directionLo := (64038295338955133571/12500000000000000000)
  directionHi := (512306362711641068569/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree106.table
  base := (21053333489423574778193370690031208726109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-115033105080011369597250249082879298850000000000)
      constant := (3064614266734829864401660050066116376087861215101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree106.table
  base := (10526660387886793028227378950285116974843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (274428)
      previous := (137214)
      next := (137214)
      square := (2060165569578365028294286719997500000000000)
      linear := (-216159952556594434579182043389827325000000000)
      constant := (5773240947374890642815122696747603381470436243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64038295338955133571/12500000000000000000)
  centralHi := (512306362711641068569/100000000000000000000)
  directionLo := (257370067926711983867/50000000000000000000)
  directionHi := (102948027170684793547/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree107.table
  base := (10843685631675035990605768666630982913779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (549606392506406048103842490523777500000000000)
      linear := (-58059191133472893985884113122838048175000000000)
      constant := (1561663663587992738530738419158643614371345899731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree107.table
  base := (43374719397001912422036994934482333068533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-872797233491778941257044945218289300000000000)
      constant := (23535364014110287093652041547451561446404691933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257370067926711983867/50000000000000000000)
  centralHi := (102948027170684793547/20000000000000000000)
  directionLo := (517162455754447807953/100000000000000000000)
  directionHi := (258581227877223903977/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree108.table
  base := (44658293818905083013038536749959418886793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-26045257656417823632508045201882865300000000000)
      constant := (707243639750484995208499202944799270234409989153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree108.table
  base := (22329136390517143882066077423070150600971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (6776)
      previous := (3388)
      next := (3388)
      square := (50868285668601605636895968395000000000000)
      linear := (-5437991708377655211094825412822650000000000)
      constant := (148036749549382164211700004239067688222717491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517162455754447807953/100000000000000000000)
  centralHi := (258581227877223903977/50000000000000000000)
  directionLo := (64946685325535115363/12500000000000000000)
  directionHi := (103914696520856184581/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree109.table
  base := (22978660018322218010599504313911028147499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-118288936640814624720804180571269691350000000000)
      constant := (3242421420767944273284693498078719763175956012811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree109.table
  base := (359041413305136902425447784075827786589/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (137214)
      previous := (68607)
      next := (68607)
      square := (1030082784789182514147143359998750000000000)
      linear := (-111139010002822668392209811067031162500000000)
      constant := (3054091502540235264881788776404281097681740624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64946685325535115363/12500000000000000000)
  centralHi := (103914696520856184581/20000000000000000000)
  directionLo := (26098668644641187663/5000000000000000000)
  directionHi := (521973372892823753261/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree110.table
  base := (11817955110500284896118482863304974767989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54022500000000000000000000000000000000000000
      center := (605052)
      previous := (302526)
      next := (302526)
      square := (4542201590962033455403656946477500000000000)
      linear := (-493281875321277037583975858405233425000000000)
      constant := (13647944016047764658287186839083660512261474301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree110.table
  base := (1890872121671671256263959572230565055953/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9072)
      previous := (4536)
      next := (4536)
      square := (68104646928210414158488817190000000000000)
      linear := (-7415450440396550000644588927233300000000000)
      constant := (205683469314106925199977384328579894238304825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26098668644641187663/5000000000000000000)
  centralHi := (521973372892823753261/100000000000000000000)
  directionLo := (131090569882209838523/25000000000000000000)
  directionHi := (524362279528839354093/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree111.table
  base := (9720358873993823714332503623628293270797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-26768775781040769215520029977080730300000000000)
      constant := (747497660301029947935844763726410053996626076185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree111.table
  base := (12150444636852896596865907912567751930179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (30492)
      previous := (15246)
      next := (15246)
      square := (228907285508707225366031857777500000000000)
      linear := (-25150747959816215361619778662616925000000000)
      constant := (704079353352392739211424409968996206851964931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131090569882209838523/25000000000000000000)
  centralHi := (524362279528839354093/100000000000000000000)
  directionLo := (131685087988411410743/25000000000000000000)
  directionHi := (526740351953645642973/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree112.table
  base := (49947241221252754595774115827172075459639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (5976432)
      previous := (2988216)
      next := (2988216)
      square := (44865827959706616171742244124390000000000000)
      linear := (-4961010947004811422218698451414697300000000000)
      constant := (139805407281538187670602818846000936718601796679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree112.table
  base := (49947226834470704491907178219136454554777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-913584349818784955958628803513189300000000000)
      constant := (25810202815621525567243182993820477991091369377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131685087988411410743/25000000000000000000)
  centralHi := (526740351953645642973/100000000000000000000)
  directionLo := (132276934062552149927/25000000000000000000)
  directionHi := (529107736250208599709/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree113.table
  base := (51308160455777391931796966002343906582631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-245260090777104596437752178444913762700000000000)
      constant := (6974562944613295826418828909841089826858632866759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree113.table
  base := (51308147375527497146038612161438413705649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-921741773084186158898945575172169300000000000)
      constant := (26277738066643643316430270352412123792729065849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132276934062552149927/25000000000000000000)
  centralHi := (529107736250208599709/100000000000000000000)
  directionLo := (132866143811965443937/25000000000000000000)
  directionHi := (531464575247861775749/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree114.table
  base := (52684551586840665680500575030336254550303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-27492293905663714798532014752278595300000000000)
      constant := (788863656098940900369385683620389151958208577863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree114.table
  base := (52684539695401399305269360966149155789791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-103322132927731929093251371870127700000000000)
      constant := (2972162496566138571241169803942024230655082399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132866143811965443937/25000000000000000000)
  centralHi := (531464575247861775749/100000000000000000000)
  directionLo := (133452752155716133963/25000000000000000000)
  directionHi := (533811008622864535853/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree115.table
  base := (27038207087920685800922864997925785352307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-124800599762421134967912043548050476350000000000)
      constant := (3613047418240041141231640481051498544652038237523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree115.table
  base := (54076403365998036172689738019626374968101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-938056619614988564779579118490129300000000000)
      constant := (27225376018780584074079444804518452601062357901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133452752155716133963/25000000000000000000)
  centralHi := (533811008622864535853/100000000000000000000)
  directionLo := (536147172994999368413/100000000000000000000)
  directionHi := (268073586497499684207/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree116.table
  base := (2774187391376442329865602829005311000469/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (549606392506406048103842490523777500000000000)
      linear := (-62942938474677776671215010355423636925000000000)
      constant := (1838382184587170200697212799848091981997526445705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree116.table
  base := (55483738001646680273799639467537213577789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-946214042880389767719895890149109300000000000)
      constant := (27705478711919695315179444541656511030275909989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536147172994999368413/100000000000000000000)
  centralHi := (268073586497499684207/50000000000000000000)
  directionLo := (538473202020397301217/100000000000000000000)
  directionHi := (269236601010198650609/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree117.table
  base := (56906552185721461024579829195560256851041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (32538352)
      previous := (16269176)
      next := (16269176)
      square := (244269507780624910268374440232790000000000000)
      linear := (-28215812030286660381543999527476460300000000000)
      constant := (831341623284995497252592727052761738980621282361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree117.table
  base := (71133179068624156210163162599578592653/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12717071417150401409223992098750000000000)
      linear := (-1472795472447208288055883737358162500000000)
      constant := (43502732322696362579301381686884288471101300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538473202020397301217/100000000000000000000)
  centralHi := (269236601010198650609/50000000000000000000)
  directionLo := (13519730662019247221/2500000000000000000)
  directionHi := (540789226480769888841/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree118.table
  base := (14586206732361974973691176582539595790863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (73211292)
      previous := (36605646)
      next := (36605646)
      square := (549606392506406048103842490523777500000000000)
      linear := (-64028215661612195045732987518220434425000000000)
      constant := (1902933112322419533324939996081661475641315786607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree118.table
  base := (29172409406372836366635082324326014718533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-481264444705596086800264716733534650000000000)
      constant := (14339125757637706528342917381787362970256341933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13519730662019247221/2500000000000000000)
  centralHi := (540789226480769888841/100000000000000000000)
  directionLo := (271547687184608171791/50000000000000000000)
  directionHi := (543095374369216343583/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree119.table
  base := (5979857176946948450985891342165016633721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (2988216)
      previous := (1494108)
      next := (1494108)
      square := (22432913979853308085871122062195000000000000)
      linear := (-2635545071635894050326203106106891150000000000)
      constant := (79005125069046608013284819100870843487959931405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree119.table
  base := (29899282196601430730349053201598382239433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-485343156338296688270423102563024650000000000)
      constant := (14585460809830245799774727016141021594328682833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271547687184608171791/50000000000000000000)
  centralHi := (543095374369216343583/100000000000000000000)
  directionLo := (545391770972765115041/100000000000000000000)
  directionHi := (272695885486382557521/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree120.table
  base := (1225355728902918175728103845997109072451/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-14469665077454802982277992151337162650000000000)
      constant := (437465779517451916111485701735734208620938424275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree120.table
  base := (61267779742242828826583420365832957362421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-108760415104666064386795886309447700000000000)
      constant := (3296420095085861060126920682834316090567676469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545391770972765115041/100000000000000000000)
  centralHi := (272695885486382557521/50000000000000000000)
  directionLo := (547678538951800539597/100000000000000000000)
  directionHi := (273839269475900269799/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree121.table
  base := (62752470721610480021918002448025537577471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (2420208)
      previous := (1210104)
      next := (1210104)
      square := (18168806363848133821614627785910000000000000)
      linear := (-2170450626182275127520990190493078700000000000)
      constant := (66176675804283268508584147495471636541511570839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree121.table
  base := (31376232315511943965197641380692872667591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (4536)
      previous := (2268)
      next := (2268)
      square := (34052323464105207079244408595000000000000)
      linear := (-4078517186807420588518511357206650000000000)
      constant := (124664583559377312017157969005928272686074871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547678538951800539597/100000000000000000000)
  centralHi := (273839269475900269799/50000000000000000000)
  directionLo := (137488949604129259697/25000000000000000000)
  directionHi := (549955798416517038789/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree122.table
  base := (64252624387224302420570271039456092804757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-264795080141924127179075767375256117700000000000)
      constant := (8141483479225620691088234625789716754989577275573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree122.table
  base := (64252618853396396816153468788469117012923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-995158582472796985361796520102989300000000000)
      constant := (30674066714429698859768718910781050415843658323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137488949604129259697/25000000000000000000)
  centralHi := (549955798416517038789/100000000000000000000)
  directionLo := (552223667000535707067/100000000000000000000)
  directionHi := (138055916750133926767/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree123.table
  base := (32884123625640929777402278175793349159817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-14831424139766275773783984538936095150000000000)
      constant := (459816730640974137700719290445335676166259194657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree123.table
  base := (657682422236553862286512545087106110783/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (30492)
      previous := (15246)
      next := (15246)
      square := (228907285508707225366031857777500000000000)
      linear := (-27869889048283283008392035882276925000000000)
      constant := (866208148142606199786707674395224488866067175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552223667000535707067/100000000000000000000)
  centralHi := (138055916750133926767/25000000000000000000)
  directionLo := (554482259931810959481/100000000000000000000)
  directionHi := (277241129965905479741/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree124.table
  base := (6729933914194317176727467555906128646397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-134568094444830900338573838013221653850000000000)
      constant := (4206515394402354373771266410102798419171595627665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree124.table
  base := (33649667287257848231729168920466759591433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (548856)
      previous := (274428)
      next := (274428)
      square := (4120331139156730056588573439995000000000000)
      linear := (-505736714501799695621215031710474650000000000)
      constant := (15848554537921060327773689605539061310755634833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554482259931810959481/100000000000000000000)
  centralHi := (277241129965905479741/50000000000000000000)
  directionLo := (556731690100948176293/100000000000000000000)
  directionHi := (278365845050474088147/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree125.table
  base := (34422949952185077875881824871115944452389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (146422584)
      previous := (73211292)
      next := (73211292)
      square := (1099212785012812096207684981047555000000000000)
      linear := (-135653371631765318713091815176018451350000000000)
      constant := (4275236195311145032337571117981972665184272542021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree125.table
  base := (68845895755287594682721862885078340818381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-1019630852269000594182746835079929300000000000)
      constant := (32214913941077681177902631868654690318360952181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556731690100948176293/100000000000000000000)
  centralHi := (278365845050474088147/50000000000000000000)
  directionLo := (558972068127046954471/100000000000000000000)
  directionHi := (69871508515880869309/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree126.table
  base := (35203964699523511361081478907077018691143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (332024)
      previous := (166012)
      next := (166012)
      square := (2492545997761478676207902451355000000000000)
      linear := (-310064963307709154393672998500714850000000000)
      constant := (9851503352183093006514075025395448868819786847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree126.table
  base := (2200247675944782029054800653024295710599/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (1694)
      previous := (847)
      next := (847)
      square := (12717071417150401409223992098750000000000)
      linear := (-1586093017800002773338061121510662500000000)
      constant := (50519919641219345791598353575700984123929916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558972068127046954471/100000000000000000000)
  centralHi := (69871508515880869309/12500000000000000000)
  directionLo := (112240700484235725557/20000000000000000000)
  directionHi := (280601751210589313893/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree127.table
  base := (71985427500266542593505935397501929922873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-275647852011268310924255539003224092700000000000)
      constant := (8828691486485617337029717226796032930298106881497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree127.table
  base := (71985424077084608015642326495035978752117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-1035945698799803000063380378397889300000000000)
      constant := (33263091033941142757276163448257633727749498717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112240700484235725557/20000000000000000000)
  centralHi := (280601751210589313893/50000000000000000000)
  directionLo := (281713049623800561221/50000000000000000000)
  directionHi := (563426099247601122443/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree128.table
  base := (73578394094765796004489192465856214688107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (292845168)
      previous := (146422584)
      next := (146422584)
      square := (2198425570025624192415369962095110000000000000)
      linear := (-277818406385137147673291493328817687700000000000)
      constant := (8969468979906530671166164399590898025726631803723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree128.table
  base := (73578390985711278851389269442172269347881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1097712)
      previous := (548856)
      next := (548856)
      square := (8240662278313460113177146879990000000000000)
      linear := (-1044103122065204203003697150056869300000000000)
      constant := (33793463259291306661926646503225360811878581681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell055.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281713049623800561221/50000000000000000000)
  centralHi := (563426099247601122443/100000000000000000000)
  directionLo := (565639962782808950187/100000000000000000000)
  directionHi := (141409990695702237547/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree129.table
  base := (37593414540248326612152925601784552706407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (16269176)
      previous := (8134588)
      next := (8134588)
      square := (122134753890312455134187220116395000000000000)
      linear := (-15554942264389221356795969314133960150000000000)
      constant := (506186579812300217326502332568581271886818068047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree129.table
  base := (75186826256916043922288808737557053971527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (121968)
      previous := (60984)
      next := (60984)
      square := (915629142034828901464127431110000000000000)
      linear := (-116917838370067267327112657968427700000000000)
      constant := (3814224955843155339274394699390027931774992903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell055.Kernel129
