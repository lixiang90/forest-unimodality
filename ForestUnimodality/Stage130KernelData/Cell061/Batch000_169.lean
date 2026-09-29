import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell061.Parameters
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch000_049
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch050_099
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch100_149
import ForestUnimodality.BinomialMassData.Q3193_6468.Batch150_199
import ForestUnimodality.BinomialMassData.Q49_99.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_99.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_99.Batch100_149
import ForestUnimodality.BinomialMassData.Q49_99.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel000
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
  base := (879381023382099517482402009/10000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78392012471522002498014458750000000000)
      linear := (1007435233996400021595427062500000000)
      constant := (109922627922762439685300251125000000000000) }

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
  base := (879381023382099517482402009/10000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (78392012471522002498014458750000000000)
      linear := (1007435233996400021595427062500000000)
      constant := (109922627922762439685300251125000000000000) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel001
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
  base := (12370175632751098452036731570159574154853/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (204970732697151393189530927134578750000000000)
      linear := (-199738025247196332913660169258083312500000000)
      constant := (161769462038105231974560240890741293968142178585) }

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
  base := (493805626918056512465830310498353693879133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-6005483458162462012992635985223500000000000)
      constant := (4841255606652863941009546659584593053709382533) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel002
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
  base := (7294252311773513273426204619755669959843/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (204970732697151393189530927134578750000000000)
      linear := (-402110180318935479003385664106787687500000000)
      constant := (95558212200925757609508968038684144564409669135) }

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
  base := (290716024291174399724389486769515594254761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-12089957898152113758878526215563500000000000)
      constant := (2855252576086890405610592656055819339290912561) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel003
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
  base := (4561935618659021571146350287435149165413/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (22774525855239043687725658570508750000000000)
      linear := (-67164703932297180565901239883943562500000000)
      constant := (6676208663954965262797920044301741478424750865) }

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
  base := (181630231406955964639654049551185030045973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-2019381370904640611640490716211500000000000)
      constant := (199288043595541062685885763240429997720064597) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel004
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
  base := (121899971144839397651590362409565319288373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-6454835923699310169462693230433571500000000000)
      constant := (325082710589072138665646996885529528624796710997) }

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
  base := (121278200909851253914503674370192630456573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-24258906778131417250650306676243500000000000)
      constant := (1212583321340056324431607998747211971104871973) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel005
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
  base := (3476325209517970629190558185553181160303/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-8073813164273223338180497189223206500000000000)
      constant := (237176043531057956797065288056069731121287269175) }

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
  base := (43231828778537709112498762961408391332813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-15171690609060534498268098453291750000000000)
      constant := (442439334686458189081278458997034893452900213) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel006
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
  base := (32777918501154003080299244503621221255901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (91098103420956174750902634282035000000000000)
      linear := (-538488355824840917049905619334046750000000000)
      constant := (10318432101155116108657563598890833195485614421) }

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
  base := (32617543727730316665311661871473318716259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-2023769758783928930134560396495750000000000)
      constant := (38518980488417326665808764780893944082006051) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel007
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
  base := (5165673843247311089222945748715636059393/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (4695768)
      previous := (2347884)
      next := (2347884)
      square := (16732304709971542301186198133435000000000000)
      linear := (-115426200463480098730776582722474250000000000)
      constant := (1577291064334970124554469473746155028826349365) }

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
  base := (51417808055947654026998946610297965399453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-42512330098100372488307977367263500000000000)
      constant := (577454195932513167649461372853269858880038853) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel008
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
  base := (10493986660305822371573223127637836278311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-3232686221498740711083477266398027875000000000)
      constant := (33811514302053038718393858750218958250700710279) }

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
  base := (41790157707367706077424801314056202386113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-48596804538090024234193867597603500000000000)
      constant := (505640804952815084863375025326412839586293513) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel009
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
  base := (17399198313497675662674898227943983809821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (91098103420956174750902634282035000000000000)
      linear := (-808317895920493111836206279132319250000000000)
      constant := (6847889718726393369179303847179311745413006741) }

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
  base := (6929490293349182112242034308408899615719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-675077518247897234321972318863500000000000)
      constant := (5693751342300257324995172998763884267509995) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel010
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
  base := (29195596962738489718832239799793508251957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-16168699367142789181769516983171381500000000000)
      constant := (116194681170511802826339742094640634547801196373) }

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
  base := (14534144055643867787065379467678376641233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-30382876709034663862982824029141750000000000)
      constant := (217541351934210617919930493679008269460724633) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel011
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
  base := (24649197211766952819824972478255454662947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (3803184)
      previous := (1901592)
      next := (1901592)
      square := (13551783979976951615836755513030000000000000)
      linear := (-147005591799311589673448933404636500000000000)
      constant := (931311824161775947157465002169356119811621723) }

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
  base := (24538807254471038600552269320011877906187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (14256)
      previous := (7128)
      next := (7128)
      square := (50798024081546257618713369270000000000000)
      linear := (-552481221967429582411996184203500000000000)
      constant := (3489842931659609451350406871914462110401147) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel012
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
  base := (417145404290492670930978853955550784133/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (91098103420956174750902634282035000000000000)
      linear := (-1078147436016145306622506938930591750000000000)
      constant := (6219706554076207939712125088772056483927582325) }

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
  base := (1267076887357047770562348998750294153/610351562500000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (85368901581487460720337745578750000000000)
      linear := (-1012981976361786544690797618318937500000000)
      constant := (5830917563732078177971675451240566041199616) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel013
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
  base := (17634218397734153880939462097512025757569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-21025631088864528687922928859540286500000000000)
      constant := (113507362986627308499959159155318806866032331041) }

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
  base := (17547204323870676705168077223958921792653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-79019176738038282963623318749303500000000000)
      constant := (425944282541420474043791976837511892489792053) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel014
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
  base := (14858715288445769680388141427113869400927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9391536)
      previous := (4695768)
      next := (4695768)
      square := (33464609419943084602372396266870000000000000)
      linear := (-462134863866090650135525159557753500000000000)
      constant := (2388355811614512097938436760289020935102865647) }

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
  base := (14780618374250464582079357476593835144883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-85103651178027934709509208979643500000000000)
      constant := (439445229042562697580871625799235178254998283) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel015
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
  base := (12446345666565536572621335950548367906363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-2695953952223595002817615197457728500000000000)
      constant := (13588912641490097832788352668134314892524485123) }

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
  base := (1237610483842881109205119704838049960997/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-5066006978778754803077505511665750000000000)
      constant := (25528130823469476862696752227516932037628665) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel016
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
  base := (10334990350488891722887409088338077762851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-25882562810586268194076340735909191500000000000)
      constant := (129157277658696218794460555536101934207671118339) }

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
  base := (5135905794409197564436480687032852007969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-48636300029003619100640494720161750000000000)
      constant := (242760723589300398862415645175836982530104169) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel017
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
  base := (8476825140351598378378937090630348824799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-27501540051160181362794144694698826500000000000)
      constant := (137475581015648286366118255825762850388364872511) }

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
  base := (8420060494405359592737233467361213132763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-103357074497996889947166879670663500000000000)
      constant := (517023212748946526734528382685731749914210163) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel018
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
  base := (3416891979602168468345733473712924624617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (91098103420956174750902634282035000000000000)
      linear := (-1617806516207449696195108258527136750000000000)
      constant := (8175310716199696871565387669218302199868355457) }

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
  base := (3391434224816054060702456503424317053821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (37941734036216649209038998035000000000000)
      linear := (-675565116901151491932424505561750000000000)
      constant := (3417527031579739312415601202760842363512341) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel019
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
  base := (1074972525972124870306120131073195897727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-30739494532308007700229752612278096500000000000)
      constant := (158116247005491442590804268975598008543159559515) }

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
  base := (666160364039732682010861420009112051249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-14440752922247024179867332516417937500000000)
      constant := (74383322551700088229979534141194494714291449) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel020
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
  base := (81488444775523208951584816005773661311/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-16179235886440960434473778285533865750000000000)
      constant := (85145252786061375196450221247015291967989931975) }

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
  base := (4033702055936895698153624775877718341993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-121610497817965845184824550361683500000000000)
      constant := (641053893140216718489586859227547517469873393) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel021
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
  base := (2911052874673933321448617471333708698849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (1043504)
      previous := (521752)
      next := (521752)
      square := (3718289935549231622485821807430000000000000)
      linear := (-77046369645024566978833017074506500000000000)
      constant := (416377297804946685074389612679750308875475721) }

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
  base := (2874746951980636474802048683854482848179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-14188330250883944103412271176891500000000000)
      constant := (76821309157494807681415146365184031821666931) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel022
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
  base := (14934123584122636472206788743190681041/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (3803184)
      previous := (1901592)
      next := (1901592)
      square := (13551783979976951615836755513030000000000000)
      linear := (-294185340942394605011431111476421500000000000)
      constant := (1636899664549843208234603318573897678326871125) }

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
  base := (1834457320688092402571781882340408176191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (14256)
      previous := (7128)
      next := (7128)
      square := (50798024081546257618713369270000000000000)
      linear := (-1105615261966488832037986205143500000000000)
      constant := (6164497682176635381983383893796573062271471) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel023
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
  base := (231596580100624022229010078889323892357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-9303850873650915093775242111859159125000000000)
      constant := (53394561115590631644812886489195489773783031973) }

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
  base := (56105483870562346087910934215640655877/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-17482990142241850052810277631587937500000000)
      constant := (100555345531909852279206370026529425636500954) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel024
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
  base := (77085222920770782238371796848109251699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-4314931192797508171535419156247363500000000000)
      constant := (25569888480497530473255354205781938547912845179) }

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
  base := (25817998268128921336395002165270943417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-8108244198773580676020450626835750000000000)
      constant := (48160107889061910640037475536875980057381113) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel025
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
  base := (-692003688511732585263429418505248667107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-40453357975751486712536576365015906500000000000)
      constant := (247688704193880148226712518463393561117850665277) }

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
  base := (-178633993907098306289914792876649624219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-38008217504478525978563500378345875000000000)
      constant := (233278882239866112671980468604444082033029581) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel026
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
  base := (-69504602525618405802960821094881439337/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-10518083804081349970313595080951385375000000000)
      constant := (66558320626408563875165435020291047783806894035) }

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
  base := (-176251572619638966806148301033704355307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-19764668057237969457517486467965437500000000)
      constant := (125381688594659934263676511317998788613636093) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel027
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
  base := (-2024994533183429434419582264520165819987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-4854590272988812561108020475843908500000000000)
      constant := (31749144258642777785221711114547048905811556773) }

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
  base := (-2042582130485600594202919102244356048903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-2027182949356708733407725703383500000000000)
      constant := (13291599360001216513258843857177932918082737) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel028
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
  base := (-2603343915541053717755121986131038922479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9391536)
      previous := (4695768)
      next := (4695768)
      square := (33464609419943084602372396266870000000000000)
      linear := (-924699789744351555483469147783363500000000000)
      constant := (6248947122571417494396876877117572132057598081) }

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
  base := (-654713047732650741475248304140123473277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-42571573334470764787977918051100875000000000)
      constant := (288437221601632710338979461876352149838412123) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel029
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
  base := (-313077184930711928244594182072202204119/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-23464633469023569693703896100087223250000000000)
      constant := (163793444761234300341419428667913628330571480045) }

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
  base := (-25155444456604690484838003748959855173/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-176370767777872710897797562434743500000000000)
      constant := (1234386561499903620869404365593722057431178375) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel030
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
  base := (-3612061290155879430758952943696251769587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-5394249353180116950680621795440453500000000000)
      constant := (38877248215067052527391122598646494989647815173) }

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
  base := (-1812038910969078782910416004005493003127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-10136402345436797924649080703615750000000000)
      constant := (73249217492669517251106850932735518119594697) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel031
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
  base := (-4051275311403797160122196881137639089151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-50167221419194965724843400117753716500000000000)
      constant := (373112818572297324098208576664939814087626860961) }

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
  base := (-1015459066757829840261888855568296180393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-47134929164463003597392335723855875000000000)
      constant := (351501832027466242883940422604121004135968207) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel032
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
  base := (-2225933055711295551124025966239261050703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-25893099329884439446780602038271675750000000000)
      constant := (198615308503720902060235435231913446762598423633) }

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
  base := (-4461138894859893513686423460619822290961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-194624191097841666135455233125763500000000000)
      constant := (1496917154367794845284567358030417121726291239) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel033
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
  base := (-2408383673533339597104453500654419834749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (211288)
      previous := (105644)
      next := (105644)
      square := (752876887776497311990930861835000000000000)
      linear := (-24520282782526534463856293863789250000000000)
      constant := (193866372195009132980643304552130862976767651) }

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
  base := (-4824901747192150845973572172700552550389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1584)
      previous := (792)
      next := (792)
      square := (5644224897949584179857041030000000000000)
      linear := (-184305477996172009073775136231500000000000)
      constant := (1461144915993085499942703351890195027046499) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel034
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
  base := (-5148472395317233257202730863690431898761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-55024153140916705230996811994122621500000000000)
      constant := (448137324066796063464323021435969835559060499671) }

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
  base := (-1288900530384381744489269604547951763381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-51698284994455242406806753396610875000000000)
      constant := (422198006390750196370695066412202774767102819) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel035
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
  base := (-5449100719984885980531232382645343419003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9391536)
      previous := (4695768)
      next := (4695768)
      square := (33464609419943084602372396266870000000000000)
      linear := (-1155982252683482008157441141896168500000000000)
      constant := (9692125949937321637595081366995246829818580917) }

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
  base := (-1091068974273677292898035686919135444729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-212877614417810621373112903816783500000000000)
      constant := (1789712160838504228417979735987825267531055355) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel036
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
  base := (-11172762055791806221160052758980637289/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (22774525855239043687725658570508750000000000)
      linear := (-809195939195340716228228054329192937500000000)
      constant := (6980094302775588407541646833849153109046395584) }

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
  base := (-2862959313135055621319107631974883901707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (37941734036216649209038998035000000000000)
      linear := (-1351617832455557241475301197821750000000000)
      constant := (11690924006076630307889042802904039047893453) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel037
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
  base := (-5964064768540481397369933852459459832011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-59881084862638444737150223870491526500000000000)
      constant := (531091173081509069709324141422813644181298990421) }

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
  base := (-5968843478921145818151605187884145701057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-225046563297789924864884684277463500000000000)
      constant := (2001429711572388995262056029920441987983940343) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel038
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
  base := (-6181235240333824069612395088716694755907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-61500062103212357905868027829281161500000000000)
      constant := (560483915151790660033661852788006844855372282077) }

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
  base := (-6185411444442648762772930762911714237161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-231131037737779576610770574507803500000000000)
      constant := (2112199565562226409408423971901405288761585039) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel039
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
  base := (-6373073466838356349500242623578837449037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-7013226593754030119398425754230088500000000000)
      constant := (65638013250214719659824526234449284065468321723) }

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
  base := (-3188360397648707827666350235494750416207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-13178639565431623797592025818785750000000000)
      constant := (123679360376973249602722830354537966796750577) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel040
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
  base := (-3270260855050972702526620899881400547103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-32369008292180092121651817873430215750000000000)
      constant := (310931660829861422332959179582370318184895804033) }

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
  base := (-261748208188967407946572510873007283477/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-243299986617758880102542354968483500000000000)
      constant := (2343507324310852367557346815057681390366048075) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel041
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
  base := (-1671095361753177877917468423031339971433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-16589248456233524353005359926412516625000000000)
      constant := (163461356690589660225348335717240475033933820663) }

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
  base := (-6687158488257394176344263305108080290779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-249384461057748531848428245198823500000000000)
      constant := (2464028297952175018617598344164804205070075021) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel042
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
  base := (-3402667231656007208992069595966136352103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29645000000000000000000000000000000000000000
      center := (521752)
      previous := (260876)
      next := (260876)
      square := (1859144967774615811242910903715000000000000)
      linear := (-77070261979034025601745174222720750000000000)
      constant := (778556294673652579892346485335968902568381313) }

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
  base := (-3403877805913936913073521583287211725939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-14192718638763232421906340857175750000000000)
      constant := (143765821798244353837129874804096726430452429) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel043
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
  base := (-6903960775416503728052426405665205179333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-69594948306081923749457047623229336500000000000)
      constant := (720385480516587215220306537395080212334854977563) }

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
  base := (-690607053267367378787012693433724747999/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-130776704968863917670100012829751750000000000)
      constant := (1357385591102316147194954986822203068724309005) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel044
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
  base := (-174518846484853517245356384061595370101/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27011250000000000000000000000000000000000000
      center := (475398)
      previous := (237699)
      next := (237699)
      square := (1693972997497118951979594439128750000000000)
      linear := (-73568104903570079460924433452498937500000000)
      constant := (779897337106600101900568614844790990737437455) }

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
  base := (-3491295676416544612835247673047703369753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (25399012040773128809356684635000000000000)
      linear := (-1105941670982303665644983123511750000000000)
      constant := (11756126791623138279662861394490136027050007) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel045
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
  base := (-87951669919338659587751815737880597227/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (22774525855239043687725658570508750000000000)
      linear := (-1011568094267079862317953549177897312500000000)
      constant := (10977096936927619580274373112534034878880147330) }

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
  base := (-1759433297964663690336605901058798942313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (5324)
      previous := (2662)
      next := (2662)
      square := (18970867018108324604519499017500000000000)
      linear := (-844822095116380058123369771975875000000000)
      constant := (9192639592241251497239507107042510327980127) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel046
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
  base := (-7070457259341243979633841994206016791443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-74451880027803663255610459499598241500000000000)
      constant := (826615617755467597818044885392664261911598693773) }

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
  base := (-707184912349937775164315325607568447373/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-139903416628848395288928848175261750000000000)
      constant := (1557532677334458168784006698442306608236486135) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel047
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
  base := (-1771007223288108392761255937473526913781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-19017714317094394106082065864596969125000000000)
      constant := (215933435562164589004790292196158906512332870891) }

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
  base := (-442827466793755376018422429490378104289/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-35736413462210805290467948322607937500000000)
      constant := (406866265059433970450554759401539545899727022) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel048
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
  base := (-1415421447402562848269170221933339983249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-8632203834327943288116229713019723500000000000)
      constant := (100189408489823953007983604779362818673632586355) }

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
  base := (-7078159692889964326864868274840924880269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-32441753570852899341069941867911500000000000)
      constant := (377556335721017813696531024596530232805387059) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel049
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
  base := (-44061953118786600385712192793172429811/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (85368901581487460720337745578750000000000)
      linear := (-4128946884086078860983125331943312500000000)
      constant := (48965422972672100202997779587207485728716420) }

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
  base := (-1762706779484335043586291586788600366351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-74515064144416436453878841760385875000000000)
      constant := (886073481934587634705456832956144052809393849) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel050
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
  base := (-7002632102136922698813512955938493860303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-80927788990099315930481675334756781500000000000)
      constant := (980202756347798255580921366403020616676898209233) }

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
  base := (-7003426627288957937244076597144626989703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-304144731017655397561401257271883500000000000)
      constant := (3693789027180380868609821347774310510873920897) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel051
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
  base := (-6935425573521128145491937637572256126373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-9171862914519247677688831032616268500000000000)
      constant := (113414332773417794602914257256268881577909989667) }

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
  base := (-1734028878951724098409687430032473119879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (170737803162974921440675491157500000000000)
      linear := (-8617477929379029147424642986172875000000000)
      constant := (106846966060230779959134086534810011772451769) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel052
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
  base := (-3424214351420265899669160366451984633131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-42082871735623571133958641626168025750000000000)
      constant := (531053102625091697015439680802811124501583338741) }

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
  base := (-684902761291971810335306864437920467793/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-158156839948817350526586518866281750000000000)
      constant := (2001198934519951413465005378840580707475804035) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel053
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
  base := (-842719634950307933232580753481969375891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (204970732697151393189530927134578750000000000)
      linear := (-10723090088977631929579385901390710812500000000)
      constant := (138041760623181831591630080085424829318270937101) }

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
  base := (-6742276788286740409665878579023526020327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-322398154337624352799058927962903500000000000)
      constant := (4161509183758634144531896313163620921474775073) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel054
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
  base := (-6615509102250352420929944627350057295099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-9711521994710552067261432352212813500000000000)
      constant := (127490264098360697320312689121227836754570543421) }

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
  base := (-1323191986540648317314043173611337371897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-4055341096019925982036355780163500000000000)
      constant := (53380540403676759370013309043124140890002315) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel055
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
  base := (-101090133409216821845567868048963471179/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 27011250000000000000000000000000000000000000
      center := (475398)
      previous := (237699)
      next := (237699)
      square := (1693972997497118951979594439128750000000000)
      linear := (-91965573546455456378172205711472062500000000)
      constant := (1230724030913062064927429239639446774310343912) }

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
  base := (-6470159492999868686588303801782603382293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (14256)
      previous := (7128)
      next := (7128)
      square := (50798024081546257618713369270000000000000)
      linear := (-2765017381963666580915956267963500000000000)
      constant := (37101990312364179739551947150423109126034267) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel056
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
  base := (-788075837739675454510413381943261942597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 66701250000000000000000000000000000000000000
      center := (1173942)
      previous := (586971)
      next := (586971)
      square := (4183076177492885575296549533358750000000000)
      linear := (-231228705187609170772419640529322937500000000)
      constant := (3153365698051068542421130641993960724481081483) }

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
  base := (-3152472813915365087919722293517006577039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-170325788828796654018358299326961750000000000)
      constant := (2329029830714204972999791875179437818538440761) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel057
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
  base := (-1224016861670713989344514460850712581373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-10251181074901856456834033671809358500000000000)
      constant := (142416410363459502369070725642098823900734673335) }

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
  base := (-612037804117940609806353178618871370973/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-19263114005421275543477916049125750000000000)
      constant := (268332204913117057416876542842290495385052015) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel058
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
  base := (-5916253049920583692335297483296830643933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-93879606914690621280224107005073861500000000000)
      constant := (1328225745669586305889732408336912921430445468163) }

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
  base := (-2958253770933803589837121976732740820521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-176410263268786305764244189557301750000000000)
      constant := (2502550205420947712084393602049178907218073679) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel059
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
  base := (-1423289234656783822932175158460069288021/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-23874646038816133612235477740965874125000000000)
      constant := (343888348938414057897727554550717268893373659531) }

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
  base := (-5693377370096464337859589417923812625353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-358905000977562263274374269344943500000000000)
      constant := (5183421404848563833875252379537150212458915247) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel060
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
  base := (-1090166689648897285825658677516077090803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-10790840155093160846406634991405903500000000000)
      constant := (158192282837898643553700449065998781337514108185) }

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
  base := (-1362756081472440327641787300986315636211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (170737803162974921440675491157500000000000)
      linear := (-10138596539376442083896115543757875000000000)
      constant := (149026175271641087727987473773823402272166221) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel061
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
  base := (-2594657243202974108157358715483916281083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-49368269318206180393188759440721383250000000000)
      constant := (736378555801671576234681632139884378297931371813) }

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
  base := (-2594739864538021776168017867273766760271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-185536974928770783383073024902811750000000000)
      constant := (2774831409333900911582869696100919061982583929) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel062
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
  base := (-4908627221999278384817538776450280976853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-100355515876986273955095322840232401500000000000)
      constant := (1522633022902230350673792576832687483032913206283) }

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
  base := (-306798139750120781767707584716241415939/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-47144803037191402314003992504495437500000000)
      constant := (717197833781984823995778870313655610764763722) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel063
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
  base := (-921758957885712000846653083683312180769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (1043504)
      previous := (521752)
      next := (521752)
      square := (3718289935549231622485821807430000000000000)
      linear := (-231234678271111535428147679816376500000000000)
      constant := (3567705711901309544307101486080282710401102995) }

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
  base := (-2304459267196513167854875435009887576681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (37941734036216649209038998035000000000000)
      linear := (-2365696905787165865789616236211750000000000)
      constant := (36596923717166116525119254117051553603221599) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel064
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
  base := (-857967377619590010386950570840706184711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-103593470358134100292530930757811671500000000000)
      constant := (1624932648234269271763270745698444119933020900605) }

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
  base := (-2144971967285234486011527039321670502409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-194663686588755261001901860248321750000000000)
      constant := (3061509772591220573372235422893640307405889391) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel065
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
  base := (-3951770292728674028243831663102292727789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-105212447598708013461248734716601306500000000000)
      constant := (1677356266898926572463098560968269745579870107379) }

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
  base := (-790372574500990180122943667973243254991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-395411847617500173749689610726983500000000000)
      constant := (6320536218171520663563966031383023714289166045) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel066
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
  base := (-3594609287790118572096379684728465174641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (422576)
      previous := (211288)
      next := (211288)
      square := (1505753775552994623981861723670000000000000)
      linear := (-98100481946080740707039980418173500000000000)
      constant := (1589191035438938875167440394562254205115686959) }

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
  base := (-3594689337872892593179517645326257282543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1584)
      previous := (792)
      next := (792)
      square := (5644224897949584179857041030000000000000)
      linear := (-368683491329191758949105143211500000000000)
      constant := (5988293410500762929738038791421063684457113) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel067
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
  base := (-50286969333502301708552695674540693411/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (204970732697151393189530927134578750000000000)
      linear := (-13556300259981979974835542829272572062500000000)
      constant := (223093866063908013675497463940155083576087086568) }

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
  base := (-1609217619155095628454420879285575718061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-203790398248739738620730695593831750000000000)
      constant := (3362582673033566109489531336069146822387284139) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel068
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
  base := (-2823050899916459069629388085506478691893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-110069379320429752967402146592970211500000000000)
      constant := (1839721912569382394555856751001828000235572983723) }

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
  base := (-564622141876970214294845609201904703977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-413665270937469128987347281418003500000000000)
      constant := (6932277584928222820082020578497118659981607115) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel069
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
  base := (-602168174143861106909293532531693070923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (12782924)
      previous := (6391462)
      next := (6391462)
      square := (45549051710478087375451317141017500000000000)
      linear := (-3102454348916768503781109737548884625000000000)
      constant := (52653943519528022261933768688844945684842379117) }

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
  base := (-60218109459666150166357618838937697467/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (85368901581487460720337745578750000000000)
      linear := (-5829857574686927510183794050671437500000000)
      constant := (99202613278646327209941633715219296737292185) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel070
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
  base := (-1975238939179799788901134934820651667193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9391536)
      previous := (4695768)
      next := (4695768)
      square := (33464609419943084602372396266870000000000000)
      linear := (-2312394567379134271527301112460193500000000000)
      constant := (39841042270836102591415848768986173956386914327) }

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
  base := (-987641794410985452350635542914997611177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-212917109908724216239559530939341750000000000)
      constant := (3678048493748182130115740007364937608412854223) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel071
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
  base := (-1522756024719037733055703237775062051681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-114926311042151492473555558469339116500000000000)
      constant := (2009729209547124959547807726345764152279152257791) }

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
  base := (-6091178365892797858707401022292808181/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-215959347128719042112502476054511750000000000)
      constant := (3786402008982895439402281895495625273377252375) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel072
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
  base := (-1051229400788723875893179578751161991221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-12949476475858378404697040269792083500000000000)
      constant := (229788485254189821918946525365415040667148483859) }

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
  base := (-32851959593968537483092612559933461179/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (9485433509054162302259749508750000000000)
      linear := (-675930815891092185140263645585437500000000)
      constant := (12025785795251483742819957483387492204789364) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel073
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
  base := (-560663706491606737325288962853265527503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-118164265523299318810991166386918386500000000000)
      constant := (2127312532362908413722730127167364971261158708433) }

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
  base := (-560692464371995712032396333307843792819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-444087643137417387716776732569703500000000000)
      constant := (8015812475179650363906932109633450322986580981) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel074
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
  base := (-25531446208549521853242566332280313019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-59891621381936615989854485172854010750000000000)
      constant := (1093688847221581163966191461339955937445632663909) }

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
  base := (-25543859296790288933369868565599973481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-225086058788703519731331311400021750000000000)
      constant := (4121056909876376944035092653989313054659912719) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel075
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
  base := (477569677191918494916489184964144274219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-13489135556049682794269641589388628500000000000)
      constant := (249810204970224587375400634125849918158690378099) }

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
  base := (95509649792974292137031083979097825399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-50695176890821854578727612558931500000000000)
      constant := (941290355209069949242365750434003687659297555) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel076
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
  base := (1025231137438492711447599903490846209207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-123021197245021058317144578263287291500000000000)
      constant := (2310054975738670739481877318255870713683905241623) }

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
  base := (1025212645262474185427191539051621839257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-462341066457386342954434403260723500000000000)
      constant := (8704310579191683603415711494850610945646557857) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel077
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
  base := (1591919048684307594961949822878223467111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (77616)
      previous := (38808)
      next := (38808)
      square := (276567019999529624812995010470000000000000)
      linear := (-21022124217506320034721265343578500000000000)
      constant := (400179976570115570651021849808485046548995951) }

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
  base := (795951546470418645762426427130579068247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (25399012040773128809356684635000000000000)
      linear := (-1935642730980892540083968154921750000000000)
      constant := (36942999766043084650395708437144826904528007) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel078
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
  base := (68050979170556245261366522293346047131/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (22774525855239043687725658570508750000000000)
      linear := (-1753599329530123397980280363623146687500000000)
      constant := (33835113268565453871346933999371862216584181004) }

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
  base := (136101098030785016304267373746000516041/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (85368901581487460720337745578750000000000)
      linear := (-6590416879685633978419530329463937500000000)
      constant := (127490267633631418842270095045572164123937298) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel079
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
  base := (1391183111362439240628428996783515746903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-63939064483371398911648995069828098250000000000)
      constant := (1250219096935344571092750843633307778254754058167) }

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
  base := (2782354349629038847909870352269757562201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-480594489777355298192092073951743500000000000)
      constant := (9421590541028640006948155705405187393867132001) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel080
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
  base := (1703061105066059606429864601615636693439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-64748553103658355496007897049222915750000000000)
      constant := (1282798596373749440078091641203437422490331325471) }

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
  base := (425763996309772417368058115828904561971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-60834870527168118742247245522760437500000000)
      constant := (1208384967904618455727732963194824093611877771) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel081
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
  base := (404889801303886927623614807389345537479/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (91098103420956174750902634282035000000000000)
      linear := (-7284226858216145786707422114290859250000000000)
      constant := (146200286034079749272583133473326536399469682795) }

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
  base := (253055573965413946561432566789138071517/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (9485433509054162302259749508750000000000)
      linear := (-760437405335392903833123232117937500000000)
      constant := (15302109358053584206379457216641533913307114) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel082
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
  base := (2355346269665267933254118181848964394687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-66367530344232268664725701008012550750000000000)
      constant := (1349231029306479474945023856511652341489179757343) }

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
  base := (4710684926754667532051875731466165724257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-498847913097324253429749744642763500000000000)
      constant := (10167651892967461900188556486658976890263442857) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel083
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
  base := (5391504859155019245374340169900614055203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-134354037929038450498169205974814736500000000000)
      constant := (2766167920314795212294197000775843913663384676867) }

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
  base := (2695749148399885500553625880833753768009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-252466193768656952587817817436551750000000000)
      constant := (5211367410613478569976868668101544370680256209) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel084
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
  base := (6091334180851683543173972903172796389139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (1043504)
      previous := (521752)
      next := (521752)
      square := (3718289935549231622485821807430000000000000)
      linear := (-308328832584155019652805011187311500000000000)
      constant := (6427942702151922716048837999450635009791205131) }

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
  base := (6091328524630217804627706114709224464911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-56779651330811506324613502789271500000000000)
      constant := (1186779515695634724331997126870744345442288079) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel085
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
  base := (1702544957612686948929498409702424878859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-34397998102546569208901203473098501625000000000)
      constant := (726031622713336423430148660818421913291578959851) }

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
  base := (6810174955917471275425479277794441633113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-517101336417293208667407415333783500000000000)
      constant := (10942494346655654049416159672574885822446140513) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel086
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
  base := (754804123421334585816411383390242668777/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-69605484825380095002161308925591820750000000000)
      constant := (1487189598213844918970988359367873417441909326765) }

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
  base := (754803703390676475903218043303436992673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-261592905428641430206646652782061750000000000)
      constant := (5603585465977514131628924615005760429825940365) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel087
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
  base := (8304917903761145466877192495029262613599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-15647771876814900352560046867774808500000000000)
      constant := (338386760788341433025956875663884305903765395079) }

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
  base := (8304914284902939062085677140594614407931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-58807809477474723573242132866051500000000000)
      constant := (1275005043612905433917655617122643035090236859) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel088
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
  base := (363232376936455013222200318729397465079/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (3803184)
      previous := (1901592)
      next := (1901592)
      square := (13551783979976951615836755513030000000000000)
      linear := (-1177263835800892697039324179907131500000000000)
      constant := (25763896212963749603393524093860865745572302775) }

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
  base := (4540403152957229218442604873467671591073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 405000000000000000000000000000000000000000
      center := (7128)
      previous := (3564)
      next := (3564)
      square := (25399012040773128809356684635000000000000)
      linear := (-2212209750980422164896963165391750000000000)
      constant := (48537676547063206337008671485484881398876913) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel089
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
  base := (4937857719695061047284533815199465067979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-72033950686240964755238014863776273250000000000)
      constant := (1595115489761651746268845051567055237744128943531) }

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
  base := (9875712754134643250633570884875456432511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-541439234177251815650950976255143500000000000)
      constant := (12020387924214621081068397636756440848495040311) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel090
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
  base := (167025557041332890638754443992891180743/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (22774525855239043687725658570508750000000000)
      linear := (-2023428869625775592766581023421419187500000000)
      constant := (45331659160722009789301062247004800691015096824) }

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
  base := (10689633337986909896859591306217991985509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-6759551958237548980207862549203500000000000)
      constant := (151825382581905953726774988100117377030246589) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel091
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
  base := (11522569801022073607540731314220356457757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9391536)
      previous := (4695768)
      next := (4695768)
      square := (33464609419943084602372396266870000000000000)
      linear := (-3006241956196525629549217094798608500000000000)
      constant := (68130140433569225900803452407825528440942371277) }

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
  base := (5761283904750726040553285944907590985069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-276804091528615559571361378357911750000000000)
      constant := (6289260958359113687232628794730086049244661269) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel092
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
  base := (2474903534519714857914895212627048181461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-148924833094203669016629441603921451500000000000)
      constant := (3413723243972227711933933466377857650412680403145) }

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
  base := (12374515957825391506624462840128632035667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-559692657497220770888608646946163500000000000)
      constant := (12862385704899587388671401058762362722581572267) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel093
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
  base := (6622739540005003145920297709347417060283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (91098103420956174750902634282035000000000000)
      linear := (-8363545018598754565852624753483949250000000000)
      constant := (193884363737184462649539483972927451826770477443) }

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
  base := (6622738801848935686832023852574574999659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-31432062885400579035249696509805750000000000)
      constant := (730524852884529257610714576309440962174628651) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel094
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
  base := (3533863466403603522050238498178108572627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-38040696893837873838516262380375180375000000000)
      constant := (891740697680996307340004577076989460463153518003) }

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
  base := (14135452594746629782610465414500863333467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-571861606377200074380380427406843500000000000)
      constant := (13439706856290644580551516280532141961531310067) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel095
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
  base := (15044441895375400534613011613866826200001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-153781764815925408522782853480290356500000000000)
      constant := (3644855973985758923726696811445637080430054414689) }

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
  base := (752222040074196228832912729185340640181/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-144486520204297431531566579409295875000000000)
      constant := (3433291054184457964617128113154929493072069905) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel096
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
  base := (3194488611071091471869855104764007539507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-17266749117388813521277850826564443500000000000)
      constant := (413733121861858917914027926068102877171925565735) }

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
  base := (199655526423723020047861274494563114403/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (85368901581487460720337745578750000000000)
      linear := (-8111535489683046914891002887048937500000000)
      constant := (194858603224789745835282076131083792315848670) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel097
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
  base := (16919457248729374865777778355150320982169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-157019719297073234860218461397869626500000000000)
      constant := (3803189158783731431142204935685867681868546480441) }

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
  base := (16919456438550477313071472969076572552691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-590115029697169029618038098097863500000000000)
      constant := (14329672501715949212863057157237123987588924491) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel098
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
  base := (8942742196620309555658842706110367567389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-33035963460567919206359072335830750000000000)
      constant := (808752428124049808204240915155135815280886621) }

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
  base := (17885483696107646122977589318890858447687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-596199504137158681363923988328203500000000000)
      constant := (14632723424553540043753371964363862303645780287) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel099
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
  base := (18870524419034999463234086960352170891977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (422576)
      previous := (211288)
      next := (211288)
      square := (1505753775552994623981861723670000000000000)
      linear := (-147160398327108412486367373108768500000000000)
      constant := (3640879797775895795168609864904454562311636777) }

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
  base := (18870523819235965317202569105803581152939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (176)
      previous := (88)
      next := (88)
      square := (627136099772176019984115670000000000000)
      linear := (-61451278295801278758270572243500000000000)
      constant := (1524229384760504000490598885367303581152939) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel100
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
  base := (19874577266815687935515144269076209956439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-161876651018794974366371873274238531500000000000)
      constant := (4047055978407478693097841432005504443834791532471) }

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
  base := (4968644187703176641692666845771633741101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-152092113254284496213923942197220875000000000)
      constant := (3812104706902142086918932253594370282296530901) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel101
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
  base := (653051340195998306018510242185452596057/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (204970732697151393189530927134578750000000000)
      linear := (-20436953532421110941886209654128520812500000000)
      constant := (516255349451090595040084474860938229545476725092) }

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
  base := (835905697696076857122934739776349215073/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-614452927457127636601581659019223500000000000)
      constant := (15561063306791425229659672919093778466423261825) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel102
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
  base := (10969860617370488448727444800167142400063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (91098103420956174750902634282035000000000000)
      linear := (-9173033638885711150211526732878766750000000000)
      constant := (234104363959452154379913041575874548752208702823) }

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
  base := (21939720852957259285220123720629893983641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-68948600210790809816385283249951500000000000)
      constant := (1764100626353775008041538680181948954548185049) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel103
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
  base := (23000812276068343692670089458220929074439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-166733582740516713872525285150607436500000000000)
      constant := (4298563245297188138468512025975692162320715834471) }

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
  base := (11500405973858889880358995441268367851279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-313310938168553470046676719739951750000000000)
      constant := (8097972909222762949589223147855149023310385479) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel104
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
  base := (24080915979637505947354809077132246997127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-168352559981090627041243089109397071500000000000)
      constant := (4384096877609820108251160082152632768768670998503) }

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
  base := (12040457848634035223826597492294074014793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-316353175388548295919619664855121750000000000)
      constant := (8259091925143888626536652766290376219418986193) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel105
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
  base := (25180032319543406826618188217089302418619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (1043504)
      previous := (521752)
      next := (521752)
      square := (3718289935549231622485821807430000000000000)
      linear := (-385422986897198503877462342558246500000000000)
      constant := (10137141605760319775591417161964973724039992051) }

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
  base := (25180032076738245013033590008198056589199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-70976758357454027065013913326731500000000000)
      constant := (1871513303607442153123196645457860183625637711) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel106
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
  base := (6574540318472187036376656400785926446687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-42897628615559613344669674256744085375000000000)
      constant := (1139427739207844063032139634508365140797461585343) }

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
  base := (13149080532561513510706225959911080816431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-322437649828537947665505555085461750000000000)
      constant := (8586126732388629779970512891538749003081840231) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel107
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
  base := (5487060564836952567021824589105333296261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-173209491702812366547396500985765976500000000000)
      constant := (4645791403634703425650746961766076952055336889145) }

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
  base := (27435302644702215490662646949865682282137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-650959774097065547076897000401263500000000000)
      constant := (17504085047044942108744245416375223052047224737) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel108
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
  base := (1786966059677561838178843659045643875069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (22774525855239043687725658570508750000000000)
      linear := (-2428173179769253884946032013118827937500000000)
      constant := (65760010951521087964635647276954139070957841898) }

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
  base := (28591456800547459455524993918410656011561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-8111657389346360479293615933723500000000000)
      constant := (220235981223749558724789178694685689377398881) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel109
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
  base := (29766623652730850201885563720122673192261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-176447446183960192884832108903345246500000000000)
      constant := (4824499111421499057293926644274150901996399721829) }

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
  base := (29766623520102508981752585905745597281569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-663128722977044850568668780861943500000000000)
      constant := (18177341760890512198226506022040359098956657769) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel110
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
  base := (7740200726705447889592315913382121695319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54022500000000000000000000000000000000000000
      center := (950796)
      previous := (475398)
      next := (475398)
      square := (3387945994994237903959188878257500000000000)
      linear := (-367905833521764681928822134012675375000000000)
      constant := (10155219777565700207647011675549495205214148271) }

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
  base := (30960802792826017287828966341933234651953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (14256)
      previous := (7128)
      next := (7128)
      square := (50798024081546257618713369270000000000000)
      linear := (-5530687581958962829045906372663500000000000)
      constant := (153047660266462976805738431973931592006808193) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel111
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
  base := (32173994707860410690591320079337898378973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-19965044518345335469140857424547168500000000000)
      constant := (556289174582913676954288231629898134074957614933) }

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
  base := (32173994609887592388723098535929968252003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-75033074650780461562271173480291500000000000)
      constant := (2095932208121299063407351891564079235426431267) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel112
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
  base := (33406199048104413208502063318311925397923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9391536)
      previous := (4695768)
      next := (4695768)
      square := (33464609419943084602372396266870000000000000)
      linear := (-3700089345013916987571133077137023500000000000)
      constant := (104059749145194447787343333971828444651158569203) }

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
  base := (16703099481954589556416000276142155473073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-340691073148506902903163225776481750000000000)
      constant := (9605605351683607005502537730891985265791588473) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel113
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
  base := (3465741592109445444759862387008177869503/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-91461677573127922779851662369251893250000000000)
      constant := (2596050891464912135016678573733218827052164647835) }

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
  base := (17328707924372514664801218103316556165753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-343733310368501728776106170891651750000000000)
      constant := (9781114691504176518541761657062275816980545153) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel114
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
  base := (35927645321459947476789724998686628383323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-20504703598536639858713458744143713500000000000)
      constant := (587347199519785518152991923770238013214551381283) }

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
  base := (1796382262964726014919478482272963544743/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (170737803162974921440675491157500000000000)
      linear := (-19265308199360919702724950889267875000000000)
      constant := (553234608665697706817234737358281536501125635) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel115
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
  base := (9304221811188449463309493579551900633513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-46540327406850917974284733164020764125000000000)
      constant := (1345249186586909088172221451339140338265539472457) }

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
  base := (7443377438268586841182952835625893252797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-699635569616982761043984122243983500000000000)
      constant := (20273860290196198786727913235899824398853316985) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel116
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
  base := (19262570843655886172381765319153767279109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-93890143433988792532928368307436345750000000000)
      constant := (2738358817464471753821808772478786930363246232101) }

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
  base := (38525141641426038332422781330806017003329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-705720044056972412789870012474323500000000000)
      constant := (20634472517667644116119590294847535772649627529) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel117
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
  base := (19926204323066422627173612708166988699311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (91098103420956174750902634282035000000000000)
      linear := (-10522181339363972124143030031870129250000000000)
      constant := (309627081189674687742356065553197792098912531031) }

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
  base := (1594096344268596948698211070193221745083/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-8787710104900766228836492625983500000000000)
      constant := (259238056720391695023136166528148995778876075) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel118
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
  base := (41198688118777408068330634328040253196811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-191018241349125411403292344532451961500000000000)
      constant := (5670706225796860150300291678518580322340916556779) }

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
  base := (20599344042459043363195333329924911210927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-358944496468475858140820896467501750000000000)
      constant := (10682645260112994650934152337484085554778295527) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel119
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
  base := (42563980103280689891278797898962325602937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9391536)
      previous := (4695768)
      next := (4695768)
      square := (33464609419943084602372396266870000000000000)
      linear := (-3931371807953047440245105071249828500000000000)
      constant := (117734161797386807257335736773210350156498321257) }

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
  base := (42563980074198186205539294025399256794523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-723973467376941368027527683165343500000000000)
      constant := (21735496295272422350455103524954269615843119923) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel120
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
  base := (21974142299039564717348798838109630824219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1452605000000000000000000000000000000000000000
      center := (25565848)
      previous := (12782924)
      next := (12782924)
      square := (91098103420956174750902634282035000000000000)
      linear := (-10792010879459624318929330691668401750000000000)
      constant := (326005031568629798266002002887794220556682928099) }

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
  base := (43948284573101290583775352173048391332663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-81117549090770113308157063710631500000000000)
      constant := (2456544435497419606589535778609229698161270007) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel121
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
  base := (9070320320389554867424777889511252409763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216090000000000000000000000000000000000000000
      center := (3803184)
      previous := (1901592)
      next := (1901592)
      square := (13551783979976951615836755513030000000000000)
      linear := (-1618803083230141743053270714122486500000000000)
      constant := (49322778068461204300586816708432648516612843335) }

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
  base := (2834475098781047139469781417087138265953/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101250000000000000000000000000000000000000
      center := (1782)
      previous := (891)
      next := (891)
      square := (6349753010193282202339171158750000000000)
      linear := (-760477702744752759833987049200437500000000)
      constant := (23228823752921456787815003743396678899084386) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel122
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
  base := (46773931113947068949221301803240614471581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-197494150311421064078163560367610501500000000000)
      constant := (6068870662214904964537149743482528043262083653309) }

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
  base := (23386965547763069525621362068860017414247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-371113445348455161632592676928181750000000000)
      constant := (11432650357658794966279307321849105530677034847) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel123
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
  base := (6026909141672204347310124715981914349847/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (22774525855239043687725658570508750000000000)
      linear := (-2765460104888819128428907837866668562500000000)
      constant := (85701862722594520056045435815553125238831900287) }

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
  base := (48215273117559832823112647989168816421361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-83145707237433330556785693787411500000000000)
      constant := (2583144209659940546200025534925774341082862129) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel124
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
  base := (4967562765974185482224601269925285402499/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-100366052396284445207799584142594885750000000000)
      constant := (3136523253859103022581154795761396022068873539055) }

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
  base := (3104726727885013523357296840492494564469/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-94299479947111203344619641789630437500000000)
      constant := (2954311613461163251851397797892730628452721338) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel125
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
  base := (6394374336588906170536788055823952085883/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (204970732697151393189530927134578750000000000)
      linear := (-25293885254142850448039621530497425812500000000)
      constant := (797050979661030986952191935801040566424235335387) }

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
  base := (5115499468105040237691245228681079486367/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-380240157008439639251421512273691750000000000)
      constant := (12011942888782199728453974480263297550229414835) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel126
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
  base := (13163343558024695254260790245230231629419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14822500000000000000000000000000000000000000
      center := (260876)
      previous := (130438)
      next := (130438)
      square := (929572483887307905621455451857500000000000)
      linear := (-115629285302560497025529918482295375000000000)
      constant := (3673819787265556661451841161989084480830825251) }

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
  base := (52653374222087713961435482792965742684767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-9463762820455171978379369318243500000000000)
      constant := (301437981439053665013274918516359854864856807) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel127
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
  base := (54170766277835354732461452455310126679631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-205589036514290629921752580161558676500000000000)
      constant := (6585677310062607548650805094675712250317837699759) }

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
  base := (54170766269241195060968316447984467199891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-772649262896858581994614805008063500000000000)
      constant := (24812265064685844841907162643233055263026131691) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel128
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
  base := (3481698176871867967485251865499899140347/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (204970732697151393189530927134578750000000000)
      linear := (-25901001719358067886308798015043538937500000000)
      constant := (836448181658352537256015843834833425566749514166) }

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
  base := (11141434164514509961746056539983139295093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-778733737336848233740500695238403500000000000)
      constant := (25211251481932498146613314338670641741156032465) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel129
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
  base := (7157823486069051888457607752697223822811/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 363151250000000000000000000000000000000000000
      center := (6391462)
      previous := (3195731)
      next := (3195731)
      square := (22774525855239043687725658570508750000000000)
      linear := (-2900374874936645225822058167765804812500000000)
      constant := (94421424088185665396058894410180173943476874531) }

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
  base := (57262587882219997983615280891670097379647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-87202023530759765054042953940971500000000000)
      constant := (2845937305367184608027406954844197236046435583) }

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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (565639962782808950187/100000000000000000000)
  centralHi := (141409990695702237547/25000000000000000000)
  directionLo := (567845195172511183643/100000000000000000000)
  directionHi := (141961298793127795911/25000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree130.table
  base := (58837017453819782967548663848540973391543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-210445968236012369427905992037927581500000000000)
      constant := (6905948553310712775650144160251870500426160175127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree130.table
  base := (58837017448384609885522895543073970783359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-790902686216827537232272475699083500000000000)
      constant := (26018817863804305508816523235893272987647701559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (567845195172511183643/100000000000000000000)
  centralHi := (141961298793127795911/25000000000000000000)
  directionLo := (285020948293312794631/50000000000000000000)
  directionHi := (570041896586625589263/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree131.table
  base := (1510761488149588355274165542319303583957/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (204970732697151393189530927134578750000000000)
      linear := (-26508118184573285324577974499589652062500000000)
      constant := (876800438768932539097649110311244921468164721865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree131.table
  base := (60430459521318749035132552879773125012303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-796987160656817188978158365929423500000000000)
      constant := (26427397828433903671189075321994689898245581703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285020948293312794631/50000000000000000000)
  centralHi := (570041896586625589263/100000000000000000000)
  directionLo := (572230165272372692669/100000000000000000000)
  directionHi := (57223016527237269267/10000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree132.table
  base := (62042914105319667027072166154493217880939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (422576)
      previous := (211288)
      next := (211288)
      square := (1505753775552994623981861723670000000000000)
      linear := (-196220314708136084265694765799363500000000000)
      constant := (6541512768477807318033605525533427716132134539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree132.table
  base := (62042914101316306444905130708143152381259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1584)
      previous := (792)
      next := (792)
      square := (5644224897949584179857041030000000000000)
      linear := (-737439517995231258699765157171500000000000)
      constant := (24645707660419041676012348866191288371431331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (572230165272372692669/100000000000000000000)
  centralHi := (57223016527237269267/10000000000000000000)
  directionLo := (574410097605549402117/100000000000000000000)
  directionHi := (287205048802774701059/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree133.table
  base := (31837190596069990466789057442423245644617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 266805000000000000000000000000000000000000000
      center := (4695768)
      previous := (2347884)
      next := (2347884)
      square := (16732304709971542301186198133435000000000000)
      linear := (-2196968366915654172796524529737719250000000000)
      constant := (73814900382389220449913507899705595185842407737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree133.table
  base := (15918595297176114332467603003500937168817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-202289027384199123117482536597525875000000000)
      constant := (6813537826273702573766036979700040310191575417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (574410097605549402117/100000000000000000000)
  centralHi := (287205048802774701059/50000000000000000000)
  directionLo := (576581788140057902017/100000000000000000000)
  directionHi := (288290894070028951009/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree134.table
  base := (65324860786784773837999415393638405848607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-216921877198308022102777207873086121500000000000)
      constant := (7344862007957784390235477303675164304499888388223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree134.table
  base := (1020700949747448613151293741656378070227/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-101905072997098268026977004577555437500000000)
      constant := (3459040602141598768495617516637963166730358616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (576581788140057902017/100000000000000000000)
  centralHi := (288290894070028951009/50000000000000000000)
  directionLo := (289372664827880917507/50000000000000000000)
  directionHi := (115749065931152367003/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree135.table
  base := (66994352889616687018871958075102997437817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-24282317159875770585721667981319528500000000000)
      constant := (828523635147133635770265637170773345418632032657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree135.table
  base := (66994352887087060758721000615243738262963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-10139815536009577727922246010503500000000000)
      constant := (346835755287826437594327336677791992329818523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289372664827880917507/50000000000000000000)
  centralHi := (115749065931152367003/20000000000000000000)
  directionLo := (72612601650592287997/12500000000000000000)
  directionHi := (580900813204738303977/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree136.table
  base := (17170714375253881338352097717435012851601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-55039957919863962110053203947666347875000000000)
      constant := (1892353090643597917704214581996858296067939767089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree136.table
  base := (34341428749422531467596328757380492540959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-413704766428382723853793908540561750000000000)
      constant := (14259132694321041117639579715977224207393939159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72612601650592287997/12500000000000000000)
  centralHi := (580900813204738303977/100000000000000000000)
  directionLo := (583048328155990931557/100000000000000000000)
  directionHi := (291524164077995465779/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree137.table
  base := (35195187310686952908949937235521285072221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-110889404460014880804465309874727513250000000000)
      constant := (3841480473354688904089000921344546027969200454269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree137.table
  base := (70390374619511712458092076178005925244417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-833494007296755099453473707311463500000000000)
      constant := (28946032448121142667308106809501380573320531017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583048328155990931557/100000000000000000000)
  centralHi := (291524164077995465779/50000000000000000000)
  directionLo := (146296990559671525633/25000000000000000000)
  directionHi := (585187962238686102533/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree138.table
  base := (72116904251093609173666836611552481680953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-24821976240067074975294269300916073500000000000)
      constant := (866373163192245740639206380723278782780432146513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree138.table
  base := (72116904249495986525113829546019920683427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-93286497970749416799928844171311500000000000)
      constant := (3264110817417236791860217879215232693624252003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146296990559671525633/25000000000000000000)
  centralHi := (585187962238686102533/100000000000000000000)
  directionLo := (587319801583971571807/100000000000000000000)
  directionHi := (18353743799499111619/3125000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree139.table
  base := (36931223195291264194888321304790394469133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-112508381700588793973183113833517148250000000000)
      constant := (3956302464318979878400411429902726714724102894637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree139.table
  base := (36931223194605979693214605553073100958529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-422831478088367201472622743886071750000000000)
      constant := (14905580057274052977653325294865520212494542729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (587319801583971571807/100000000000000000000)
  centralHi := (18353743799499111619/3125000000000000000)
  directionLo := (589443930765433838309/100000000000000000000)
  directionHi := (58944393076543383831/10000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree140.table
  base := (75627001040252123225586384467062079440337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9391536)
      previous := (4695768)
      next := (4695768)
      square := (33464609419943084602372396266870000000000000)
      linear := (-4625219196770438798267021053588243500000000000)
      constant := (163851027070075467767931260777681052121015822657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree140.table
  base := (9453375129884549969308870176694151522077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-106468428827090506836391422250310437500000000)
      constant := (3781065090188018987894091141258053129067876677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589443930765433838309/100000000000000000000)
  centralHi := (58944393076543383831/10000000000000000000)
  directionLo := (295780216419124026061/50000000000000000000)
  directionHi := (591560432838248052123/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree141.table
  base := (77410568200515303911585200980556566311959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-25361635320258379364866870620512618500000000000)
      constant := (905071629124278421008214621915900293951516640639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree141.table
  base := (9676321024938347159401115365704489036483/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (85368901581487460720337745578750000000000)
      linear := (-11914332014676579256069684281011437500000000)
      constant := (426237210800380008198338152220308001060729987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295780216419124026061/50000000000000000000)
  centralHi := (591560432838248052123/100000000000000000000)
  directionLo := (118733877875414346049/20000000000000000000)
  directionHi := (296834694688535865123/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree142.table
  base := (79213147871784678375372385267498015514733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-229873695122899327452519639543403201500000000000)
      constant := (8263437935693462203546328985337576480438201713037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree142.table
  base := (39606573935459807654781830103007072579003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-431958189748351679091451579231581750000000000)
      constant := (15566417741460907181074943266206165818346808403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118733877875414346049/20000000000000000000)
  centralHi := (296834694688535865123/50000000000000000000)
  directionLo := (74471360064091399581/12500000000000000000)
  directionHi := (595770880512731196649/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree143.table
  base := (4051737002723555362925505892736196283097/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 54022500000000000000000000000000000000000000
      center := (950796)
      previous := (475398)
      next := (475398)
      square := (3387945994994237903959188878257500000000000)
      linear := (-478290645379076943432308767566514125000000000)
      constant := (17318347411486862472822003137663903452407215365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree143.table
  base := (81034740053729136682144427766480198816383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (14256)
      previous := (7128)
      next := (7128)
      square := (50798024081546257618713369270000000000000)
      linear := (-7190089701956140577923876435483500000000000)
      constant := (260989997003236140633597877282520396104127023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74471360064091399581/12500000000000000000)
  centralHi := (595770880512731196649/100000000000000000000)
  directionLo := (149466246241936856759/25000000000000000000)
  directionHi := (597864984967747427037/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree144.table
  base := (82875344748982519312924956209074307654991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-25901294400449683754439471940109163500000000000)
      constant := (944619032946456677310326588414975050934235640311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree144.table
  base := (41437672374173078530617062151487564525661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (10648)
      previous := (5324)
      next := (5324)
      square := (37941734036216649209038998035000000000000)
      linear := (-5407934125781991738732561351381750000000000)
      constant := (197715689142226314556738009298141995307604981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149466246241936856759/25000000000000000000)
  centralHi := (597864984967747427037/100000000000000000000)
  directionLo := (37496986255671616281/6250000000000000000)
  directionHi := (599951780090745860497/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree145.table
  base := (84734961955722946868424311804372186036451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-234730626844621066958673051419772106500000000000)
      constant := (8621911383769924599275990127552993892985462028739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree145.table
  base := (42367480977588593723660413327051665242707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-441084901408336156710280414577091750000000000)
      constant := (16241645746936534200522156619424799621043771307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37496986255671616281/6250000000000000000)
  centralHi := (599951780090745860497/100000000000000000000)
  directionLo := (120406268377958546423/20000000000000000000)
  directionHi := (150507835472448183029/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree146.table
  base := (86613591675091747109665686320491090930197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-236349604085194980127390855378561741500000000000)
      constant := (8743100408916129142132796952493831415303185863733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree146.table
  base := (43306795837311856522481490483644954637899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-444127138628330982583223359692261750000000000)
      constant := (16469919597946362150856743839763834700406048099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120406268377958546423/20000000000000000000)
  centralHi := (150507835472448183029/25000000000000000000)
  directionLo := (604103745064698576249/100000000000000000000)
  directionHi := (483282996051758861/80000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree147.table
  base := (5531952119217686253014407006270042361379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151250000000000000000000000000000000000000
      center := (2662)
      previous := (1331)
      next := (1331)
      square := (9485433509054162302259749508750000000000)
      linear := (-1376559427355320082466267870663562500000000)
      constant := (51281516798311780211607325734118225251453718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree147.table
  base := (5531952119192601295341930195592097827523/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1361250000000000000000000000000000000000000
      center := (23958)
      previous := (11979)
      next := (11979)
      square := (85368901581487460720337745578750000000000)
      linear := (-12421371551342383568226841800206437500000000)
      constant := (463883121487548760380899903310015276568345094) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604103745064698576249/100000000000000000000)
  centralHi := (483282996051758861/80000000000000000)
  directionLo := (151542265759581935847/25000000000000000000)
  directionHi := (606169063038327743389/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree148.table
  base := (45213944326642459228376873312193130482009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-119793779283171403232413231648070505750000000000)
      constant := (4494012636447907295824076118668377203896873630201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree148.table
  base := (11303486081617593935554230933863300347443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-112552903267080158582277312480650437500000000)
      constant := (4232816018438656071222000023122586456705288843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151542265759581935847/25000000000000000000)
  centralHi := (606169063038327743389/100000000000000000000)
  directionLo := (4865818943895608471/800000000000000000)
  directionHi := (152056841996737764719/25000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree149.table
  base := (3694542236515186750440320976035189678911/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-241206535806916719633544267254930646500000000000)
      constant := (9111761111731309800322605845528226906409053091975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree149.table
  base := (1847271118251691157360903974558429634431/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-453253850288315460202052195037771750000000000)
      constant := (17164334698556847993586174947623622471176455775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4865818943895608471/800000000000000000)
  centralHi := (152056841996737764719/25000000000000000000)
  directionLo := (76284841358709640469/12500000000000000000)
  directionHi := (610278730869677123753/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree150.table
  base := (94318235686642885059251583312154859819417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-26980612560832292533584674579302253500000000000)
      constant := (1026260654273913545933651463625919660779596846257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree150.table
  base := (47159117843194924689361305029973964083623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-50699565278701142897221682239215750000000000)
      constant := (1933222694217808117197057654653129146887065447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76284841358709640469/12500000000000000000)
  centralHi := (610278730869677123753/100000000000000000000)
  directionLo := (306161610728498105949/50000000000000000000)
  directionHi := (612323221456996211899/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree151.table
  base := (96291927974943561138484651363918159443429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-244444490288064545970979875172509916500000000000)
      constant := (9361779603098515734884862057815917369896979928581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree151.table
  base := (96291927974726611453076308278326997715253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-918676649456610223895876170536223500000000000)
      constant := (35270545443933425164164280683485886404607194653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306161610728498105949/50000000000000000000)
  centralHi := (612323221456996211899/100000000000000000000)
  directionLo := (122872181671693849727/20000000000000000000)
  directionHi := (153590227089617312159/25000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree152.table
  base := (98284632778143887654756686736402016428299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-246063467528638459139697679131299551500000000000)
      constant := (9488062255632138280692877802835961784932892684011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree152.table
  base := (98284632777957885801428930505501884645501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-924761123896599875641762060766563500000000000)
      constant := (35746280241155891322826950760872995971410555301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122872181671693849727/20000000000000000000)
  centralHi := (153590227089617312159/25000000000000000000)
  directionLo := (154097964762398239969/25000000000000000000)
  directionHi := (616391859049592959877/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree153.table
  base := (25074087524149790899787522037417780743403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (12782924)
      previous := (6391462)
      next := (6391462)
      square := (45549051710478087375451317141017500000000000)
      linear := (-6880067910255899230789318974724699625000000000)
      constant := (267088717946306070755294573714454928391854182963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree153.table
  base := (100296350096439701765377535984551467559513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-11491920967118389227007999395023500000000000)
      constant := (447224850464091778137185688809371227574701073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154097964762398239969/25000000000000000000)
  centralHi := (616391859049592959877/100000000000000000000)
  directionLo := (618416139897870953553/100000000000000000000)
  directionHi := (309208069948935476777/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree154.table
  base := (1279088499133221910418597388565564707811/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 551250000000000000000000000000000000000000
      center := (9702)
      previous := (4851)
      next := (4851)
      square := (34570877499941203101624376308750000000000)
      linear := (-5255975333314772421089839919229187500000000)
      constant := (205413526193372984431091848537282921611446510) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree154.table
  base := (6395442495657565621080966672776184070897/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 101250000000000000000000000000000000000000
      center := (1782)
      previous := (891)
      next := (891)
      square := (6349753010193282202339171158750000000000)
      linear := (-967902967744399978443733307052937500000000)
      constant := (37920809280210200144437398664220866819485314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618416139897870953553/100000000000000000000)
  centralHi := (309208069948935476777/50000000000000000000)
  directionLo := (620433816188119232671/100000000000000000000)
  directionHi := (19388556755878726021/3125000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree155.table
  base := (52188411140330538946784772347423933756573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-125460199625180099322925545503834228250000000000)
      constant := (4936001920322088772738208615722905697930040100797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree155.table
  base := (6523551392533993164681306938272416641801/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-117876818402071103859927466432197937500000000)
      constant := (4649083966014420251001373757915055598512583202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620433816188119232671/100000000000000000000)
  centralHi := (19388556755878726021/3125000000000000000)
  directionLo := (622444952147033438361/100000000000000000000)
  directionHi := (311222476073516719181/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree156.table
  base := (106445577146943644459795568943479158900569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-28059930721214901312729877218495343500000000000)
      constant := (1111298027198691513259576737704074087222952206449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree156.table
  base := (53222788573421595485285286674839079420793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5445000000000000000000000000000000000000000
      center := (95832)
      previous := (47916)
      next := (47916)
      square := (341475606325949842881350982315000000000000)
      linear := (-52727723425364360145850312315995750000000000)
      constant := (2093399884567243435909289408034246757489243577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (622444952147033438361/100000000000000000000)
  centralHi := (311222476073516719181/50000000000000000000)
  directionLo := (312224805483521989159/50000000000000000000)
  directionHi := (624449610967043978319/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree157.table
  base := (108533344529833090916865483931929093979421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-254158353731508024983286698925247726500000000000)
      constant := (10132209586837062291595320648474684322557958315069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree157.table
  base := (54266672264873492614585805069692118641351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-477591748048274067185595755959131750000000000)
      constant := (19086460982765874159455021375183809704803881151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312224805483521989159/50000000000000000000)
  centralHi := (624449610967043978319/100000000000000000000)
  directionLo := (125289570965896821581/20000000000000000000)
  directionHi := (313223927414742053953/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree158.table
  base := (110640124429650258292653820528615346011289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-255777330972081938152004502884037361500000000000)
      constant := (10263585866791532461760139488101676146196911224121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree158.table
  base := (55320062214788227047774270707250368229219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49005000000000000000000000000000000000000000
      center := (862488)
      previous := (431244)
      next := (431244)
      square := (3073280456933548585932158840835000000000000)
      linear := (-480633985268268893058538701074301750000000000)
      constant := (19333921929041304658765825710708822359014575419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125289570965896821581/20000000000000000000)
  centralHi := (313223927414742053953/50000000000000000000)
  directionLo := (314219872463547497503/50000000000000000000)
  directionHi := (628439744927094995007/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree159.table
  base := (22553183369341855320838511033013653822393/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2905210000000000000000000000000000000000000000
      center := (51131696)
      previous := (25565848)
      next := (25565848)
      square := (182196206841912349501805268564070000000000000)
      linear := (-28599589801406205702302478538091888500000000000)
      constant := (1155090120516939498014527831071269325110677183765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree159.table
  base := (28191479211661504743833210657532520908811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2722500000000000000000000000000000000000000
      center := (47916)
      previous := (23958)
      next := (23958)
      square := (170737803162974921440675491157500000000000)
      linear := (-26870901249347984385082313677192875000000000)
      constant := (1087943433329612402400795262463943790269695179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314219872463547497503/50000000000000000000)
  centralHi := (628439744927094995007/100000000000000000000)
  directionLo := (630425341485890812603/100000000000000000000)
  directionHi := (157606335371472703151/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree160.table
  base := (57455360890658832132689707542457616873831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-129507642726614882244720055400808315750000000000)
      constant := (5264442620210317708860634728821420233806220303559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree160.table
  base := (114910721781263448249081623824671715285963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-973436919416517089608849182609283500000000000)
      constant := (39667281190885076263498817067706967481517723363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630425341485890812603/100000000000000000000)
  centralHi := (157606335371472703151/25000000000000000000)
  directionLo := (632404703786405962449/100000000000000000000)
  directionHi := (12648094075728119249/2000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree161.table
  base := (117074539233776437743135852647633375496193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 533610000000000000000000000000000000000000000
      center := (9391536)
      previous := (4695768)
      next := (4695768)
      square := (33464609419943084602372396266870000000000000)
      linear := (-5319066585587830156288937035926658500000000000)
      constant := (217608333348915496591358669539883156799852354673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree161.table
  base := (117074539233729972805764451835193778058579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-979521393856506741354735072839623500000000000)
      constant := (40171796631142651012685005003002722718752132779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (632404703786405962449/100000000000000000000)
  centralHi := (12648094075728119249/2000000000000000000)
  directionLo := (126875578036869127327/20000000000000000000)
  directionHi := (158594472546086409159/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree162.table
  base := (29814342301095057275090093873732933404401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 726302500000000000000000000000000000000000000
      center := (12782924)
      previous := (6391462)
      next := (6391462)
      square := (45549051710478087375451317141017500000000000)
      linear := (-7284812220399377522968769964422108375000000000)
      constant := (299932787935608266641960404586747753858079982921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree162.table
  base := (119257369204340408630808555625600290482259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (21296)
      previous := (10648)
      next := (10648)
      square := (75883468072433298418077996070000000000000)
      linear := (-12167973682672794976550876087283500000000000)
      constant := (502216171859773583030374883032894635148353339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126875578036869127327/20000000000000000000)
  centralHi := (158594472546086409159/25000000000000000000)
  directionLo := (3977155988316625431/625000000000000000)
  directionHi := (636344958130660068961/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree163.table
  base := (60729605846708704723583772649481977518021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-131936108587475751997796761338992768250000000000)
      constant := (5466600667588252108446401531896387790814616810469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree163.table
  base := (30364802923345821146944073635949826356511/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-247922585684121511211626713325075875000000000)
      constant := (10297605264846232943304168329915260623120164311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3977155988316625431/625000000000000000)
  centralHi := (636344958130660068961/100000000000000000000)
  directionLo := (39894122761941375791/6250000000000000000)
  directionHi := (638305964191062012657/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree164.table
  base := (1546000833764627708084918511424509815733/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3268361250000000000000000000000000000000000000
      center := (57523158)
      previous := (28761579)
      next := (28761579)
      square := (204970732697151393189530927134578750000000000)
      linear := (-33186399301940677145538915829596896437500000000)
      constant := (1383708905322677143819955910979336718143391020370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree164.table
  base := (123680066701140973841067050613566303374031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-997774817176475696592392743530643500000000000)
      constant := (41704530047375233195338206728207477339368877831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39894122761941375791/6250000000000000000)
  centralHi := (638305964191062012657/100000000000000000000)
  directionLo := (640260964065006203119/100000000000000000000)
  directionHi := (8003262050812577539/1250000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree165.table
  base := (62959967113957442948944755220918182825003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12005000000000000000000000000000000000000000
      center := (211288)
      previous := (105644)
      next := (105644)
      square := (752876887776497311990930861835000000000000)
      linear := (-122640115544581878022511079244979250000000000)
      constant := (5145541821807786349516268907103828931962832203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree165.table
  base := (125919934227889827628133639533729906930883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1584)
      previous := (792)
      next := (792)
      square := (5644224897949584179857041030000000000000)
      linear := (-921817531328251008575095164151500000000000)
      constant := (38771200077699975216072764736426069162377947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (640260964065006203119/100000000000000000000)
  centralHi := (8003262050812577539/1250000000000000000)
  directionLo := (642210012604148821931/100000000000000000000)
  directionHi := (160552503151037205483/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree166.table
  base := (64089407136960891024063779388824323592331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13073445000000000000000000000000000000000000000
      center := (230092632)
      previous := (115046316)
      next := (115046316)
      square := (819882930788605572758123708538315000000000000)
      linear := (-134364574448336621750873467277177220750000000000)
      constant := (5672578935562517846473178348468523383204308350059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree166.table
  base := (128178814273900310310665342828640538987649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1724976)
      previous := (862488)
      next := (862488)
      square := (6146560913867097171864317681670000000000000)
      linear := (-1009943766056455000084164523991323500000000000)
      constant := (42742341571107702039320692177162736922617947849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642210012604148821931/100000000000000000000)
  centralHi := (160552503151037205483/25000000000000000000)
  directionLo := (322076581915152134871/50000000000000000000)
  directionHi := (644153163830304269743/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree167.table
  base := (6522835341972776634570658237069076367651/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6536722500000000000000000000000000000000000000
      center := (115046316)
      previous := (57523158)
      next := (57523158)
      square := (409941465394302786379061854269157500000000000)
      linear := (-67587031534311789167616184628286019125000000000)
      constant := (2871043648066285035129574404755275169968285127695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree167.table
  base := (16307088354929641852630517684706580698419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12251250000000000000000000000000000000000000
      center := (215622)
      previous := (107811)
      next := (107811)
      square := (768320114233387146483039710208750000000000)
      linear := (-127003530062055581478756301777707937500000000)
      constant := (5408255513356889341730104582671296634925204619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322076581915152134871/50000000000000000000)
  centralHi := (644153163830304269743/100000000000000000000)
  directionLo := (161522617738228969731/25000000000000000000)
  directionHi := (25843618838116635157/4000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree168.table
  base := (132753611924775161267915626786544913002471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 59290000000000000000000000000000000000000000
      center := (1043504)
      previous := (521752)
      next := (521752)
      square := (3718289935549231622485821807430000000000000)
      linear := (-616705449836328956551434336671051500000000000)
      constant := (26358367916821653690934261380336531789191650559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree168.table
  base := (132753611924759397778257021580357688124079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (191664)
      previous := (95832)
      next := (95832)
      square := (682951212651899685762701964630000000000000)
      linear := (-113568079437381589286215144939111500000000000)
      constant := (4865882721317783388869596189039221522367122031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell061.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161522617738228969731/25000000000000000000)
  centralHi := (25843618838116635157/4000000000000000000)
  directionLo := (648021986386056550481/100000000000000000000)
  directionHi := (324010993193028275241/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 3193
  qDenominator := 6468
  table := BinomialMassData.Q3193_6468.Degree169.table
  base := (135069529530134219527151734807849392865737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26146890000000000000000000000000000000000000000
      center := (460185264)
      previous := (230092632)
      next := (230092632)
      square := (1639765861577211145516247417076630000000000000)
      linear := (-273586080618394983007900346430723346500000000000)
      constant := (11764754848285326063467883951911987218432721010793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3193_6468.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 49
  qDenominator := 99
  table := BinomialMassData.Q49_99.Degree169.table
  base := (33767382382530178420177393534319244448001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24502500000000000000000000000000000000000000
      center := (431244)
      previous := (215622)
      next := (215622)
      square := (1536640228466774292966079420417500000000000)
      linear := (-257049297344105988830455548670585875000000000)
      constant := (11080760681531248753244038123626677039834857801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_99.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell061.Kernel169
