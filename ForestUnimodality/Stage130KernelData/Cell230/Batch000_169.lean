import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell230.Parameters
import ForestUnimodality.BinomialMassData.Q123_203.Batch000_049
import ForestUnimodality.BinomialMassData.Q123_203.Batch050_099
import ForestUnimodality.BinomialMassData.Q123_203.Batch100_149
import ForestUnimodality.BinomialMassData.Q123_203.Batch150_199
import ForestUnimodality.BinomialMassData.Q63_103.Batch000_049
import ForestUnimodality.BinomialMassData.Q63_103.Batch050_099
import ForestUnimodality.BinomialMassData.Q63_103.Batch100_149
import ForestUnimodality.BinomialMassData.Q63_103.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree000.table
  base := (663473863511589886432062711/50000000000000000000000000)
  polynomial :=
    { denominator := 1015000000000000000000000000000000000000000
      center := (2091)
      previous := (0)
      next := (1360)
      square := (33547912558052444959022509355000000000000)
      linear := (-97942808156251167650552246900000000000000)
      constant := (13468519429285274694570873033300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree000.table
  base := (663473863511589886432062711/50000000000000000000000000)
  polynomial :=
    { denominator := 515000000000000000000000000000000000000000
      center := (1071)
      previous := (0)
      next := (680)
      square := (17021847258519220841277430855000000000000)
      linear := (-49695119409329410187226016900000000000000)
      constant := (6833780794169375830250245923300000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree001.table
  base := (71322278443143956854981678588352564723091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-56270353089999776985963286844060000000000000)
      constant := (2968214160008289868232523151537350839673857019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree001.table
  base := (14149226721753239884856927331884487787987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-14526700107468702150570472056860000000000000)
      constant := (758119155564453062706292792780542654713770415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48737477273829643571/100000000000000000000)
  directionHi := (12184369318457410893/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree002.table
  base := (41820722499707025493057981553839106555587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-72775926068561579905802361446720000000000000)
      constant := (1791579842456633439841687290737075742049184683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree002.table
  base := (41274928380871155289017246569937652429217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-18816205616615545802572384632320000000000000)
      constant := (455656241537720887150231342444588554621563153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48737477273829643571/100000000000000000000)
  centralHi := (12184369318457410893/25000000000000000000)
  directionLo := (34462600678250190539/50000000000000000000)
  directionHi := (68925201356500381079/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree003.table
  base := (26602489232302750619492002081173742053649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-89281499047123382825641436049380000000000000)
      constant := (1213547882738272278586679224648058736288821641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree003.table
  base := (13094308558589567469110216108782432681967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-11552855562881194727287148603890000000000000)
      constant := (154213172852086242792275719383157828322987903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34462600678250190539/50000000000000000000)
  centralHi := (68925201356500381079/100000000000000000000)
  directionLo := (84415786871006438293/100000000000000000000)
  directionHi := (42207893435503219147/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree004.table
  base := (4505131287485254782467430648947203900117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-52893536012842592872740255326020000000000000)
      constant := (459495426771497406773850851519970651039842906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree004.table
  base := (3543571541020812705795520009614880946811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-27395216634909233106576209783240000000000000)
      constant := (234004517591382190000750940728901359823589495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84415786871006438293/100000000000000000000)
  centralHi := (42207893435503219147/50000000000000000000)
  directionLo := (97474954547659287143/100000000000000000000)
  directionHi := (12184369318457410893/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree005.table
  base := (1586212707104078199982491531224872697543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-61146322502123494332659792627350000000000000)
      constant := (384205495283461839196744929041108115972197948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree005.table
  base := (3115813956737868645172135487768147412151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-15842361072028038379289061179350000000000000)
      constant := (98163291441464702753071120244589551791019918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97474954547659287143/100000000000000000000)
  centralHi := (12184369318457410893/12500000000000000000)
  directionLo := (54490156118067107557/50000000000000000000)
  directionHi := (21796062447226843023/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree006.table
  base := (9075607013644552124047624035283309621227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-138798217982808791585158659857360000000000000)
      constant := (698576720443884538259796665985469906181143443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree006.table
  base := (1779910855365060863661153905093232196121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-35974227653202920410580034934160000000000000)
      constant := (179211087881462791511246533599950501843238445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54490156118067107557/50000000000000000000)
  centralHi := (21796062447226843023/20000000000000000000)
  directionLo := (59690975335686980873/50000000000000000000)
  directionHi := (119381950671373961747/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree007.table
  base := (3224699605683070878813721030828773108819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (60639)
      previous := (0)
      next := (39440)
      square := (972889464183520903811652771295000000000000)
      linear := (-11093127925812185321785552461430000000000000)
      constant := (48532370916039802222009872561043987291617453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree007.table
  base := (6307845556068218431481623579786821110183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-40263733162349764062581947509620000000000000)
      constant := (175031142933726688317585503698928385157931447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59690975335686980873/50000000000000000000)
  centralHi := (119381950671373961747/100000000000000000000)
  directionLo := (64473622197607733953/50000000000000000000)
  directionHi := (128947244395215467907/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree008.table
  base := (277661665162942363593674695678197161303/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-85904681969966198712418404531340000000000000)
      constant := (347927618529997098372311122504182614561082616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree008.table
  base := (4326220374633371619619074575588000421049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-44553238671496607714583860085080000000000000)
      constant := (179947252381614114131125264412733096466908841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64473622197607733953/50000000000000000000)
  centralHi := (128947244395215467907/100000000000000000000)
  directionLo := (34462600678250190539/25000000000000000000)
  directionHi := (137850402713000762157/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree009.table
  base := (71340321340416310553815880252287041611/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-94157468459247100172337941832670000000000000)
      constant := (369738456623791257040071196532094933954953980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree009.table
  base := (2756837515069795056161740705946329887301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-48842744180643451366585772660540000000000000)
      constant := (191860518749187740670929161151714613774376309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34462600678250190539/25000000000000000000)
  centralHi := (137850402713000762157/100000000000000000000)
  directionLo := (73106215910744465357/50000000000000000000)
  directionHi := (29242486364297786143/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree010.table
  base := (781216279462379671791973100663866455273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-102410254948528001632257479134000000000000000)
      constant := (402685637609192287782419975818757272755345057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree010.table
  base := (296321203426326250818126385640376884449/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-53132249689790295018587685236000000000000000)
      constant := (209518115039199265857212728553293791835597205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73106215910744465357/50000000000000000000)
  centralHi := (29242486364297786143/20000000000000000000)
  directionLo := (77060717797997784189/50000000000000000000)
  directionHi := (154121435595995568379/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree011.table
  base := (19668972263562277090740579668012887829/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-221326082875617806184354032870660000000000000)
      constant := (890351983259308423957426601956008577363631525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree011.table
  base := (424219259981637627538135459494601279901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-57421755198937138670589597811460000000000000)
      constant := (232110504311186383096506462604108224978469709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77060717797997784189/50000000000000000000)
  centralHi := (154121435595995568379/100000000000000000000)
  directionLo := (6465757013830652247/4000000000000000000)
  directionHi := (1262843166763799267/781250000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree012.table
  base := (-82299756697523329518291016004748573561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-237831655854179609104193107473320000000000000)
      constant := (992235501028430117784646003220421580160623755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree012.table
  base := (-58469354990476774643159386961790774821/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-30855630354041991161295755193460000000000000)
      constant := (129540717295417369486381268887049446679696044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6465757013830652247/4000000000000000000)
  centralHi := (1262843166763799267/781250000000000000)
  directionLo := (168831573742012876587/100000000000000000000)
  directionHi := (42207893435503219147/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree013.table
  base := (-23703237623214078469403527213475366861/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-127168614416370706012016091037990000000000000)
      constant := (554729485100588362656839138508382340175626275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree013.table
  base := (-1231899072753727259845336132751637222493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-66000766217230825974593422962380000000000000)
      constant := (290032190057241380235833176644607880706571763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168831573742012876587/100000000000000000000)
  centralHi := (42207893435503219147/25000000000000000000)
  directionLo := (8786273667377683157/5000000000000000000)
  directionHi := (175725473347553663141/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree014.table
  base := (-371436574022594409660315085924825232777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-38691828830186173563410179525520000000000000)
      constant := (177267417529837870735044894791442769273209005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree014.table
  base := (-75835377574326096385048647365453890483/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-70290271726377669626595335537840000000000000)
      constant := (324669209062388117427996615254777491896646325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8786273667377683157/5000000000000000000)
  centralHi := (175725473347553663141/100000000000000000000)
  directionLo := (91179470927175890533/50000000000000000000)
  directionHi := (182358941854351781067/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree015.table
  base := (-76514703424612976503280404119266909321/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-143674187394932508931855165640650000000000000)
      constant := (692806364745921218209761889166511078940654576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree015.table
  base := (-155026105702902959148043904767509220249/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-37289888617762256639298624056650000000000000)
      constant := (181386406839756087355608790959696957459026872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91179470927175890533/50000000000000000000)
  centralHi := (182358941854351781067/100000000000000000000)
  directionLo := (188759437817704666921/100000000000000000000)
  directionHi := (94379718908852333461/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree016.table
  base := (-371855928169057855241131978392063810917/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-151926973884213410391774702941980000000000000)
      constant := (771514677982421135363814740232805769663685388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree016.table
  base := (-3001144587557633486231639498782400874489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-78869282744671356930599160688760000000000000)
      constant := (404177018049907673881466895448297509122546199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188759437817704666921/100000000000000000000)
  centralHi := (94379718908852333461/50000000000000000000)
  directionLo := (97474954547659287143/50000000000000000000)
  directionHi := (194949909095318574287/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree017.table
  base := (-86209064549625630018081729797794095037/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-160179760373494311851694240243310000000000000)
      constant := (856312638173294986596587843893739062752405340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree017.table
  base := (-693991147855836539660813955127077572663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-83158788253818200582601073264220000000000000)
      constant := (448755674681608525879578903704454170158091165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97474954547659287143/50000000000000000000)
  centralHi := (194949909095318574287/100000000000000000000)
  directionLo := (200949766726139885711/100000000000000000000)
  directionHi := (12559360420383742857/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree018.table
  base := (-484778395931526845932265958306196915171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-168432546862775213311613777544640000000000000)
      constant := (947010453396078524476895231243099725290873044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree018.table
  base := (-3895920701713106614370907894466859684291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-87448293762965044234602985839680000000000000)
      constant := (496412564662415689303947447827721085609356781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200949766726139885711/100000000000000000000)
  centralHi := (12559360420383742857/6250000000000000000)
  directionLo := (41355120813900228647/20000000000000000000)
  directionHi := (51693901017375285809/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree019.table
  base := (-4271501124076197473339882245252830749611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-353370666704112229543066629691940000000000000)
      constant := (2086925314138389362150395407329306097639280301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree019.table
  base := (-4285974026158412388476720645004742749297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-91737799272111887886604898415140000000000000)
      constant := (547074119337597997257313718745874684172708127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41355120813900228647/20000000000000000000)
  centralHi := (51693901017375285809/25000000000000000000)
  directionLo := (21244173819973361989/10000000000000000000)
  directionHi := (212441738199733619891/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree020.table
  base := (-115840140029750321901173591083861093789/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-184938119841337016231452852147300000000000000)
      constant := (1145557549121210842825310447580503363720981980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree020.table
  base := (-4645427237358106963061258309947812901857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-96027304781258731538606810990600000000000000)
      constant := (600683988741156889087334405709763652924199087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21244173819973361989/10000000000000000000)
  centralHi := (212441738199733619891/100000000000000000000)
  directionLo := (54490156118067107557/25000000000000000000)
  directionHi := (217960624472268430229/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree021.table
  base := (-4968709475380716490738932231400995352791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-55197401808747976483249254128180000000000000)
      constant := (358059780552711149818607732875332340358119383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree021.table
  base := (-2489177265005887555879242761542095060883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-50158405145202787595304361783030000000000000)
      constant := (328599474870762234965263388959764913499092253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54490156118067107557/25000000000000000000)
  centralHi := (217960624472268430229/100000000000000000000)
  directionLo := (111671589394257168763/50000000000000000000)
  directionHi := (223343178788514337527/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree022.table
  base := (-660002838483461759788999660760726729787/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-201443692819898819151291926749960000000000000)
      constant := (1366351565863084391784262848342504848768830068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree022.table
  base := (-5287884967988576419990691927389510522603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-104606315799552418842610636141520000000000000)
      constant := (716585806100112825745145764552844682865704773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111671589394257168763/50000000000000000000)
  centralHi := (223343178788514337527/100000000000000000000)
  directionLo := (228599031499206797691/100000000000000000000)
  directionHi := (57149757874801699423/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree023.table
  base := (-2785009922161684307285345990909797198549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-209696479309179720611211464051290000000000000)
      constant := (1484933564130689505877752881534883167244994259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree023.table
  base := (-43565817295682799429370278523911287841/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-54447910654349631247306274358490000000000000)
      constant := (389409515949617359844351229893833809426869184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228599031499206797691/100000000000000000000)
  centralHi := (57149757874801699423/25000000000000000000)
  directionLo := (233736729876569469123/100000000000000000000)
  directionHi := (58434182469142367281/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree024.table
  base := (-730076338734995666001001956109310581367/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-217949265798460622071131001352620000000000000)
      constant := (1608915875745367431925113159940205681009789188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree024.table
  base := (-5845825769146910433700213516203951817209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-113185326817846106146614461292440000000000000)
      constant := (843878976071654225963810004758272275171229719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233736729876569469123/100000000000000000000)
  centralHi := (58434182469142367281/25000000000000000000)
  directionLo := (59690975335686980873/25000000000000000000)
  directionHi := (238763901342747923493/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree025.table
  base := (-6093270996712990110169933320463217957187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-452404104575483047062101077307900000000000000)
      constant := (3476536189615375917567969694063281251202280917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree025.table
  base := (-762189515322115931091192866742692654857/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-58737416163496474899308186933950000000000000)
      constant := (455875246134030550163908969665032094498488348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59690975335686980873/25000000000000000000)
  centralHi := (238763901342747923493/100000000000000000000)
  directionLo := (243687386369148217857/100000000000000000000)
  directionHi := (121843693184574108929/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree026.table
  base := (-316457114879940600510620525607474212809/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-234454838777022424990970075955280000000000000)
      constant := (1872966699369290390381033851343755951643539190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree026.table
  base := (-6332597425749652440571048167442020315329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-121764337836139793450618286443360000000000000)
      constant := (982421892005601480426758709335087606474674639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243687386369148217857/100000000000000000000)
  centralHi := (121843693184574108929/50000000000000000000)
  directionLo := (24851334766254223399/10000000000000000000)
  directionHi := (248513347662542233991/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree027.table
  base := (-6549108817864164458015248009717605856459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-485415250532606652901779226513220000000000000)
      constant := (4025986941643040095520603635171717180261181069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree027.table
  base := (-1637980241822744396903396949757630562907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-63026921672643318551310099509410000000000000)
      constant := (527942071981621638070052457036727594716239274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24851334766254223399/10000000000000000000)
  centralHi := (248513347662542233991/100000000000000000000)
  directionLo := (791398001915685359/312500000000000000)
  directionHi := (253247360613019314881/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree028.table
  base := (-6753856261439546233259204086397700996059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-71702974787309779403088328730840000000000000)
      constant := (616666937307925991090244731976336734236200667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree028.table
  base := (-6756145358267566504699846714305874837471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-130343348854433480754622111594280000000000000)
      constant := (1132130260936180253177990509593848973849270161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (791398001915685359/312500000000000000)
  centralHi := (253247360613019314881/100000000000000000000)
  directionLo := (257894488790430935813/100000000000000000000)
  directionHi := (128947244395215467907/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree029.table
  base := (-694391707678625557855951228036827867891/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7105000000000000000000000000000000000000000
      center := (14637)
      previous := (0)
      next := (9520)
      square := (234835387906367114713157565485000000000000)
      linear := (-8938386146374659633473403029630000000000000)
      constant := (79619936475987321858887327755183337998634445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree029.table
  base := (-6945780817879994915455452830157788918589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-134632854363580324406624024169740000000000000)
      constant := (1211154830008913503688471209325986017362689299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257894488790430935813/100000000000000000000)
  centralHi := (128947244395215467907/50000000000000000000)
  directionLo := (262459347403545085841/100000000000000000000)
  directionHi := (131229673701772542921/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree030.table
  base := (-222490789241465218593414150604145192431/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-267465984734146030830648225160600000000000000)
      constant := (2464916572404685494638569364983560492241774736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree030.table
  base := (-7121223146751339477106007740405647700473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-138922359872727168058625936745200000000000000)
      constant := (1292953652132632807415040605961036483545681943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262459347403545085841/100000000000000000000)
  centralHi := (131229673701772542921/50000000000000000000)
  directionLo := (53389231397543767067/20000000000000000000)
  directionHi := (33368269623464854417/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree031.table
  base := (-7281543123697093382814007086076685787069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-551437542446853864581135524923860000000000000)
      constant := (5252285766052923081649689941130595855400673579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree031.table
  base := (-291311192624403467038827690007708706127/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-143211865381874011710627849320660000000000000)
      constant := (1377523465350379651224338510337235458417466425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53389231397543767067/20000000000000000000)
  centralHi := (33368269623464854417/12500000000000000000)
  directionLo := (135679394549733389651/50000000000000000000)
  directionHi := (271358789099466779303/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree032.table
  base := (-7429681985436927697042958733339780561869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-567943115425415667500974599526520000000000000)
      constant := (5585303823320888102710145194145320982825940379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree032.table
  base := (-3715345010138668362316042012833265707121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-73750685445510427681314880948060000000000000)
      constant := (732430866016843991480538177997211884113153311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135679394549733389651/50000000000000000000)
  centralHi := (271358789099466779303/100000000000000000000)
  directionLo := (275700805426001524313/100000000000000000000)
  directionHi := (137850402713000762157/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree033.table
  base := (-3782159026079204395780457234762817430917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-292224344201988735210406837064590000000000000)
      constant := (2964439615472714983754382744682344056489341347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree033.table
  base := (-236410628600213822559695744394493034953/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-75895438200083849507315837235790000000000000)
      constant := (777483237574078970121735953107786174274937968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275700805426001524313/100000000000000000000)
  centralHi := (137850402713000762157/50000000000000000000)
  directionLo := (27997549143373784341/10000000000000000000)
  directionHi := (279975491433737843411/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree034.table
  base := (-1921401185501705443629708831255399091433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-300477130691269636670326374365920000000000000)
      constant := (3141502833359099811011878936843732517682275006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree034.table
  base := (-7686275503977763392551417957975040237663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-156080381909314542666633587047040000000000000)
      constant := (1647836152107218215429892870300922798118633233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27997549143373784341/10000000000000000000)
  centralHi := (279975491433737843411/100000000000000000000)
  directionLo := (56837177091963345861/20000000000000000000)
  directionHi := (142092942729908364653/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree035.table
  base := (-3896831095196926849092808264210516964647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (60639)
      previous := (0)
      next := (39440)
      square := (972889464183520903811652771295000000000000)
      linear := (-44104273882935791161463701666750000000000000)
      constant := (474834155712786918179869531688467686629123111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree035.table
  base := (-7794209810866899098159470043778933987847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-160369887418461386318635499622500000000000000)
      constant := (1743469557470916246214883222713799289322931177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56837177091963345861/20000000000000000000)
  centralHi := (142092942729908364653/50000000000000000000)
  directionLo := (28833480397898054393/10000000000000000000)
  directionHi := (288334803978980543931/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree036.table
  base := (-7888584611717973897988181578445777702967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-633965407339662879180330897937160000000000000)
      constant := (7022892888246735142148404108759107946638432897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree036.table
  base := (-3944515981912088224689895717758698712333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-82329696463804114985318706098980000000000000)
      constant := (920932873901315628471253109361337965360859203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28833480397898054393/10000000000000000000)
  centralHi := (288334803978980543931/100000000000000000000)
  directionLo := (292424863642977861429/100000000000000000000)
  directionHi := (29242486364297786143/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree037.table
  base := (-7970446004810860692289304360168790519349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-650470980318224682100169972539820000000000000)
      constant := (7408646742103499853093038320019174311488147059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree037.table
  base := (-3985405835678897060917922452489898042853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-84474449218377536811319662386710000000000000)
      constant := (971511991782399883931536270890819671663372523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292424863642977861429/100000000000000000000)
  centralHi := (29242486364297786143/10000000000000000000)
  directionLo := (59291700116502396167/20000000000000000000)
  directionHi := (74114625145627995209/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree038.table
  base := (-200982614507116861368801468509862686567/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-333488276648393242510004523571240000000000000)
      constant := (3902468671374097235256897233220801370985209940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree038.table
  base := (-4019801831505740725030587769680485066199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-86619201972950958637320618674440000000000000)
      constant := (1023471842065846177233257906030319733932694809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59291700116502396167/20000000000000000000)
  centralHi := (74114625145627995209/25000000000000000000)
  directionLo := (150218993688088855359/50000000000000000000)
  directionHi := (300437987376177710719/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree039.table
  base := (-4047603100261693954045399485779298463333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-341741063137674143969924060872570000000000000)
      constant := (4105881400118918931240168361818885889624510403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree039.table
  base := (-404772548846890688497890413891015659941/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-88763954727524380463321574962170000000000000)
      constant := (1076812196455774172507125723490067148636859310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150218993688088855359/50000000000000000000)
  centralHi := (300437987376177710719/100000000000000000000)
  directionLo := (1521827240110267727/500000000000000000)
  directionHi := (304365448022053545401/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree040.table
  base := (-2034546764013173735263833056876522489841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-349993849626955045429843598173900000000000000)
      constant := (4314560811598528354765587143890350769432284462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree040.table
  base := (-2034596878048645414506017709495524017431/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-90908707482097802289322531249900000000000000)
      constant := (1131532875134631819640104343891923971398149042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1521827240110267727/500000000000000000)
  centralHi := (304365448022053545401/100000000000000000000)
  directionLo := (308242871191991136757/100000000000000000000)
  directionHi := (154121435595995568379/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree041.table
  base := (-8168275750626618437717731755548013739771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-716493272232471893779526270950460000000000000)
      constant := (9057012632893751482636581092421951901797776861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree041.table
  base := (-2042110003248075008028471814337833079827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-93053460236671224115323487537630000000000000)
      constant := (1187633736237754442250437627178944857712230714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308242871191991136757/100000000000000000000)
  centralHi := (154121435595995568379/50000000000000000000)
  directionLo := (156036061001695614791/50000000000000000000)
  directionHi := (312072122003391229583/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree042.table
  base := (-8185494927915041434363949062653628334557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-104714120744433385242766477936160000000000000)
      constant := (1356490699457847138822035623130118089994462941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree042.table
  base := (-1637125922706094238820326596508556666629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-190396425982489291882648887650720000000000000)
      constant := (2490229335317561560755665897589123611618664695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156036061001695614791/50000000000000000000)
  centralHi := (312072122003391229583/100000000000000000000)
  directionLo := (6317099050124718803/2000000000000000000)
  directionHi := (315854952506235940151/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree043.table
  base := (-16379725084727956179410075074537662101/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-374752209094797749809602210077890000000000000)
      constant := (4972193836622913189708927648581429370619972750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree043.table
  base := (-1637994608496985825766637623789856703681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-194685931491636135534650800226180000000000000)
      constant := (2607951161320899745299350675439437051153241355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6317099050124718803/2000000000000000000)
  centralHi := (315854952506235940151/100000000000000000000)
  directionLo := (319593011052703751699/100000000000000000000)
  directionHi := (3195930110527037517/1000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree044.table
  base := (-4090696426745189556333274327637375324637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-383004995584078651269521747379220000000000000)
      constant := (5201935188198003341931642923704231400247033867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree044.table
  base := (-8181483563521072257719378739547182258049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-198975437000782979186652712801640000000000000)
      constant := (2728432809771297226279182134100623943424358159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319593011052703751699/100000000000000000000)
  centralHi := (3195930110527037517/1000000000000000000)
  directionLo := (323287850691532612351/100000000000000000000)
  directionHi := (1262843166763799267/390625000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree045.table
  base := (-4080048602465539731070291313117160506067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-391257782073359552729441284680550000000000000)
      constant := (5436941269097770276634778227555879932705484997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree045.table
  base := (-8160171710786761847710346817097341939221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-203264942509929822838654625377100000000000000)
      constant := (2851674168911979343514086217383664299366804411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323287850691532612351/100000000000000000000)
  centralHi := (1262843166763799267/390625000000000000)
  directionLo := (163470468354201322671/50000000000000000000)
  directionHi := (326940936708402645343/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree046.table
  base := (-8125984635741377152986494922652629166469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-799021137125280908378721643963760000000000000)
      constant := (11354423786153998211742327940606287804678978979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree046.table
  base := (-1625209172989557063922248193573593451699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-207554448019076666490656537952560000000000000)
      constant := (2977675149832462758256741103618568735354626545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163470468354201322671/50000000000000000000)
  centralHi := (326940936708402645343/100000000000000000000)
  directionLo := (33055365341618114591/10000000000000000000)
  directionHi := (330553653416181145911/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree047.table
  base := (-807906236077650461961551791750721061641/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-407763355051921355649280359283210000000000000)
      constant := (5922746911477205192945973914517007678854180155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree047.table
  base := (-1009889088128078648243634738181291594211/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-105921976764111755071329225264010000000000000)
      constant := (1553217840837509564547873836245423709908062004) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33055365341618114591/10000000000000000000)
  centralHi := (330553653416181145911/100000000000000000000)
  directionLo := (83531827571067883623/25000000000000000000)
  directionHi := (334127310284271534493/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree048.table
  base := (-8019336148756868445266480954257735906093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-832032283082404514218399793169080000000000000)
      constant := (12347092410873577840829727201980312961045813563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree048.table
  base := (-400968878167572479907815022787066613847/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-108066729518685176897330181551740000000000000)
      constant := (1618977853934457696710279569030280102936971770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83531827571067883623/25000000000000000000)
  centralHi := (334127310284271534493/100000000000000000000)
  directionLo := (168831573742012876587/50000000000000000000)
  directionHi := (13506525899361030127/4000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree049.table
  base := (-7946810620254530257636789999072747546821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-121219693722995188162605552538820000000000000)
      constant := (1837031337071763784134269093855048735191864773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree049.table
  base := (-7946844704856021470709758347942841545821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-220422964546517197446662275678940000000000000)
      constant := (3372235183167532787163490601550604394040385011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168831573742012876587/50000000000000000000)
  centralHi := (13506525899361030127/4000000000000000000)
  directionLo := (68232468183361501/20000000000000000)
  directionHi := (341162340916807505001/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree050.table
  base := (-1965372370728488850533074465915086922701/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-432521714519764060029038971187200000000000000)
      constant := (6690937258026197778901793702765710366004828982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree050.table
  base := (-7861517547132028629417857470928021446753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-224712470055664041098664188254400000000000000)
      constant := (3509274071313619918616540684885924620471397423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68232468183361501/20000000000000000)
  centralHi := (341162340916807505001/100000000000000000000)
  directionLo := (21539125423906369087/6250000000000000000)
  directionHi := (344626006782501905393/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree051.table
  base := (-1940843929351147967459493660616572597311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-440774501009044961488958508488530000000000000)
      constant := (6957528878846658882578108957498268319674822002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree051.table
  base := (-7763398834120029068626895639628125031493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-229001975564810884750666100829860000000000000)
      constant := (3649072343196711408017689514547915221540890763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21539125423906369087/6250000000000000000)
  centralHi := (344626006782501905393/100000000000000000000)
  directionLo := (348055205738788096471/100000000000000000000)
  directionHi := (43506900717348512059/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree052.table
  base := (-1530494344928589175581476149855029810127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-898054574996651725897756091579720000000000000)
      constant := (14458768985485744806295094114289040382772382285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree052.table
  base := (-3826245386691936619071153198823316432029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-116645740536978864201334006702660000000000000)
      constant := (1895814987698381182972475623036243435972604339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348055205738788096471/100000000000000000000)
  centralHi := (43506900717348512059/12500000000000000000)
  directionLo := (351450946695107326281/100000000000000000000)
  directionHi := (175725473347553663141/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree053.table
  base := (-3764389721261352109614666028060839489211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-457280073987606764408797583091190000000000000)
      constant := (7506504059785507871086030395069125865489103901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree053.table
  base := (-1882198786193981654823194095591256202849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-118790493291552286027334962990390000000000000)
      constant := (1968473474515659523503454921461829725887949918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351450946695107326281/100000000000000000000)
  centralHi := (175725473347553663141/50000000000000000000)
  directionLo := (354814190279791701929/100000000000000000000)
  directionHi := (35481419027979170193/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree054.table
  base := (-57752347176587917535092477128268447829/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-465532860476887665868717120392520000000000000)
      constant := (7788887547675787906209907899939895874138543296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree054.table
  base := (-7392313386581817324296807362966486058651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-241870492092251415706671838556240000000000000)
      constant := (4085023248841609222561039219832168549403771541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354814190279791701929/100000000000000000000)
  centralHi := (35481419027979170193/10000000000000000000)
  directionLo := (179072926007060942619/50000000000000000000)
  directionHi := (358145852014121885239/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree055.table
  base := (-57944287870514003922704815228035808607/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-947571293932337134657273315387700000000000000)
      constant := (16153069860453684784336229263118734045389267125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree055.table
  base := (-3621523331955964300034826526861259004597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-123079998800699129679336875565850000000000000)
      constant := (2117929431233488418370407725071653903220230427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179072926007060942619/50000000000000000000)
  centralHi := (358145852014121885239/100000000000000000000)
  directionLo := (361446805223034658139/100000000000000000000)
  directionHi := (18072340261151732907/5000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree056.table
  base := (-1416197422229547759607144299087703349339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-137725266701556991082444627141480000000000000)
      constant := (2391270338901253362821443551388993451912206535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree056.table
  base := (-354049796153829766783969498532229231473/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-125224751555272551505337831853580000000000000)
      constant := (2194726889934007773354057655049355800833029430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361446805223034658139/100000000000000000000)
  centralHi := (18072340261151732907/5000000000000000000)
  directionLo := (91179470927175890533/25000000000000000000)
  directionHi := (364717883708703562133/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree057.table
  base := (-3453077331230509979215150692421873253681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-490291219944730370248475732296510000000000000)
      constant := (8667621298112372268702143015566872025089059671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree057.table
  base := (-3453080967439403444380772036127658251701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-127369504309845973331338788141310000000000000)
      constant := (2272903996433638219183891752402206673607704091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91179470927175890533/25000000000000000000)
  centralHi := (364717883708703562133/100000000000000000000)
  directionLo := (5749373190784134759/1562500000000000000)
  directionHi := (367959884210184624577/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree058.table
  base := (-1679634831462510329750930066044756226769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7105000000000000000000000000000000000000000
      center := (14637)
      previous := (0)
      next := (9520)
      square := (234835387906367114713157565485000000000000)
      linear := (-17191172635655561093392940330960000000000000)
      constant := (309346905238721584190627448936440802803522502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree058.table
  base := (-1343709065826236313532984364019117366787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-259028514128838790314679488858080000000000000)
      constant := (4704921494783077444086547546509925919278783585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5749373190784134759/1562500000000000000)
  centralHi := (367959884210184624577/100000000000000000000)
  directionLo := (185586784334842615151/50000000000000000000)
  directionHi := (371173568669685230303/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree059.table
  base := (-6518141665533420171647834845240759118917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1013593585846584346336629613798340000000000000)
      constant := (18559526071921210576724851358026003557468549347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree059.table
  base := (-6518146622213710372555205185087814247121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-263318019637985633966681401433540000000000000)
      constant := (4866794280137143239343649715185733378652293311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185586784334842615151/50000000000000000000)
  centralHi := (371173568669685230303/100000000000000000000)
  directionLo := (93589916580929873087/25000000000000000000)
  directionHi := (374359666323719492349/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree060.table
  base := (-6304962145779627704376865053833467471201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1030099158825146149256468688401000000000000000)
      constant := (19187459281318781189222786001348576638979277991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree060.table
  base := (-1260993247820972011807525730816728025239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-267607525147132477618683314009000000000000000)
      constant := (5031426344420877270328874078160826661901197245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93589916580929873087/25000000000000000000)
  centralHi := (374359666323719492349/100000000000000000000)
  directionLo := (188759437817704666921/50000000000000000000)
  directionHi := (377518875635409333843/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree061.table
  base := (-607900115008967167992382378153800601601/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-523302365901853976088153881501830000000000000)
      constant := (9912960058117435345827865620016065155043121955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree061.table
  base := (-6079004531017548942488463531246594752599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-271897030656279321270685226584460000000000000)
      constant := (5198817683908261686634393773169334876269677209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188759437817704666921/50000000000000000000)
  centralHi := (377518875635409333843/100000000000000000000)
  directionLo := (380651866082435907639/100000000000000000000)
  directionHi := (9516296652060897691/2500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree062.table
  base := (-292012949829786339438814642372953747091/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-531555152391134877548073418803160000000000000)
      constant := (10237454281779785148601692157446589490361269810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree062.table
  base := (-5840261789535033136368613852877787847871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-276186536165426164922687139159920000000000000)
      constant := (5368968295505889724152502069290139548721936561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380651866082435907639/100000000000000000000)
  centralHi := (9516296652060897691/2500000000000000000)
  directionLo := (9593981995340157673/2500000000000000000)
  directionHi := (383759279813606306921/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree063.table
  base := (-5588735950437704934326413167165586277131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-154230839680118794002283701744140000000000000)
      constant := (3019203516052389910891265498706006193586529803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree063.table
  base := (-5588738257955722847960817047546352032371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-280476041674573008574689051735380000000000000)
      constant := (5541878176632608548994136405143550751288576061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9593981995340157673/2500000000000000000)
  centralHi := (383759279813606306921/100000000000000000000)
  directionLo := (9671043329641160093/2500000000000000000)
  directionHi := (386841733185646403721/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree064.table
  base := (-5324432233723167849055149913224714204093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1096121450739393360935824986811640000000000000)
      constant := (21804468253503517417328345674382402752363531563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree064.table
  base := (-1331108535102350011762543244720553433801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-142382773591859926113345482155420000000000000)
      constant := (2858773662561402652120923328138159297241610382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9671043329641160093/2500000000000000000)
  centralHi := (386841733185646403721/100000000000000000000)
  directionLo := (97474954547659287143/25000000000000000000)
  directionHi := (389899818190637148573/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree065.table
  base := (-1009469606710449345226450049153721517781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1112627023717955163855664061414300000000000000)
      constant := (22485039479259725114132513754492371449868813855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree065.table
  base := (-5047349609191681708523417475950064512133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-289055052692866695878692876886300000000000000)
      constant := (5895975739148595789409059442277895765590781003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97474954547659287143/25000000000000000000)
  centralHi := (389899818190637148573/100000000000000000000)
  directionLo := (196467051891728759207/50000000000000000000)
  directionHi := (78586820756691503683/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree066.table
  base := (-4757483508491312343932711977389992875089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1129132596696516966775503136016960000000000000)
      constant := (23176138283100990893245307446412815783610457399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree066.table
  base := (-4757484810672206540100488170428603531351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-293344558202013539530694789461760000000000000)
      constant := (6077163417157144507445573944813802945135897241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196467051891728759207/50000000000000000000)
  centralHi := (78586820756691503683/20000000000000000000)
  directionLo := (395945137117664352143/100000000000000000000)
  directionHi := (24746571069854022009/6250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree067.table
  base := (-4454838793801535626356909353459430871479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1145638169675078769695342210619620000000000000)
      constant := (23877764659453337162063716227866260313217221889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree067.table
  base := (-2227419935029860402412217196866392253481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-148817031855580191591348351018610000000000000)
      constant := (3130555178910055934623383226763529444582820071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395945137117664352143/100000000000000000000)
  centralHi := (24746571069854022009/6250000000000000000)
  directionLo := (398933444697412009373/100000000000000000000)
  directionHi := (199466722348706004687/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree068.table
  base := (-4139414005666888823392472487524639842433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1162143742653640572615181285222280000000000000)
      constant := (24589918603528938608137999849503517116733178503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree068.table
  base := (-206970744762496980872737054878647969321/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-150961784610153613417349307306340000000000000)
      constant := (3223908279996416116580076796282484236934735110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398933444697412009373/100000000000000000000)
  centralHi := (199466722348706004687/50000000000000000000)
  directionLo := (200949766726139885711/50000000000000000000)
  directionHi := (401899533452279771423/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree069.table
  base := (-3811209244617187988236439931734910789003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1178649315632202375535020359824940000000000000)
      constant := (25312600111185062041731961549629066061295975373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree069.table
  base := (-476401247492073236303197903561682700439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-153106537364727035243350263594070000000000000)
      constant := (3318641011340654446403860599959821432924170596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200949766726139885711/50000000000000000000)
  centralHi := (401899533452279771423/100000000000000000000)
  directionLo := (404843891741220677677/100000000000000000000)
  directionHi := (202421945870610338839/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree070.table
  base := (-69404491966056400310639401275086800233/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (60639)
      previous := (0)
      next := (39440)
      square := (972889464183520903811652771295000000000000)
      linear := (-85368206329340298461061388173400000000000000)
      constant := (1860414941343551619236017958189839100175708225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree070.table
  base := (-3470225206129869058468892061593786634831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-310502580238600914138702439763600000000000000)
      constant := (6829506745015495536296398216693551517591077921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404843891741220677677/100000000000000000000)
  centralHi := (202421945870610338839/50000000000000000000)
  directionLo := (203883495145631067961/50000000000000000000)
  directionHi := (407766990291262135923/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree071.table
  base := (-3116460143746750369623841104099739215711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1211660461589325981374698509030260000000000000)
      constant := (26789545803228881107034685478900283846659765401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree071.table
  base := (-623292129239580916149249923460631700559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-314792085747747757790704352339060000000000000)
      constant := (7024490726227638826719939419231960791443847845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203883495145631067961/50000000000000000000)
  centralHi := (407766990291262135923/100000000000000000000)
  directionLo := (410669283076067584773/100000000000000000000)
  directionHi := (205334641538033792387/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree072.table
  base := (-687478987293657936337727836550139968013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-614083017283943892147268791816460000000000000)
      constant := (13771904990815513216510824615471370564116304566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree072.table
  base := (-687479091130913971127435047186077907963/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-159540795628447300721353132457260000000000000)
      constant := (3611116982817349952539313722634565798948841066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410669283076067584773/100000000000000000000)
  centralHi := (205334641538033792387/50000000000000000000)
  directionLo := (41355120813900228647/10000000000000000000)
  directionHi := (413551208139002286471/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree073.table
  base := (-2370592075504036941470630332989828601381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1244671607546449587214376658235580000000000000)
      constant := (28308601711505806389801146932570392153165690371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree073.table
  base := (-592648104712923157587122840599873553003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-161685548383020722547354088744990000000000000)
      constant := (3711368231312033315921636120120036882952382346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41355120813900228647/10000000000000000000)
  centralHi := (413551208139002286471/100000000000000000000)
  directionLo := (83282637672985706649/20000000000000000000)
  directionHi := (208206594182464266623/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree074.table
  base := (-989244288779000360823878190603752068203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-630588590262505695067107866419120000000000000)
      constant := (14541960495297009268898658779154349981021422573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree074.table
  base := (-1978488861384448629699633398953998427121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-327660602275188288746710090065440000000000000)
      constant := (7625998216641923386708337289209177030686673311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83282637672985706649/20000000000000000000)
  centralHi := (208206594182464266623/50000000000000000000)
  directionLo := (419255632204580542067/100000000000000000000)
  directionHi := (104813908051145135517/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree075.table
  base := (-1573605505055368408906604309297721356193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1277682753503573193054054807440900000000000000)
      constant := (29869767816846798980093652118804400200632642663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree075.table
  base := (-1573605739675975796774527001917907596003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-331950107784335132398712002640900000000000000)
      constant := (7832019227183769232915954266472902918314004173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419255632204580542067/100000000000000000000)
  centralHi := (104813908051145135517/25000000000000000000)
  directionLo := (422078934355032191467/100000000000000000000)
  directionHi := (105519733588758047867/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree076.table
  base := (-1155942903420274319487454216640124539607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1294188326482134995973893882043560000000000000)
      constant := (30666142188392264565652204911442157107847335137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree076.table
  base := (-288985774340457784173574285139074857277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-168119806646740988025356957608180000000000000)
      constant := (4020399746893337273099396578616159109678296614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422078934355032191467/100000000000000000000)
  centralHi := (105519733588758047867/25000000000000000000)
  directionLo := (424883476399467239781/100000000000000000000)
  directionHi := (212441738199733619891/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree077.table
  base := (-145100162888980807740621986397778480431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-187241985637242399841961850949460000000000000)
      constant := (4496149157644028731241117229034691390428513515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree077.table
  base := (-725500974756229882591262310892462407491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-340529118802628819702715827791820000000000000)
      constant := (8252339016022945817148553194563111866318927981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424883476399467239781/100000000000000000000)
  centralHi := (212441738199733619891/50000000000000000000)
  directionLo := (106917406852297002363/25000000000000000000)
  directionHi := (427669627409188009453/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree078.table
  base := (-70569819208282106334002747011181044501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-663599736219629300906786015624440000000000000)
      constant := (16145236780299830412490466821751692480674316582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree078.table
  base := (-282279409341575060625488308110536364123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-344818624311775663354717740367280000000000000)
      constant := (8466637793494932232060702240444175319713019093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106917406852297002363/25000000000000000000)
  centralHi := (427669627409188009453/100000000000000000000)
  directionLo := (430437744510551440679/100000000000000000000)
  directionHi := (10760943612763786017/2500000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree079.table
  base := (173721673352686054030023762786969156131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1343705045417820404733411105851540000000000000)
      constant := (33118430558180549624810091441135018211955002379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree079.table
  base := (173721563829365424913047621140141683541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-349108129820922507006719652942740000000000000)
      constant := (8683695825830758976238627926265805763120686469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430437744510551440679/100000000000000000000)
  centralHi := (10760943612763786017/2500000000000000000)
  directionLo := (43318817341929802261/10000000000000000000)
  directionHi := (433188173419298022611/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree080.table
  base := (321251001161820744676958743620319272013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-680105309198191103826625090227100000000000000)
      constant := (16978457547429230412100205630457849736880383717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree080.table
  base := (128500382360451037025008576211668180093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-353397635330069350658721565518200000000000000)
      constant := (8903513112680813494932497550789147938613033185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43318817341929802261/10000000000000000000)
  centralHi := (433188173419298022611/100000000000000000000)
  directionLo := (54490156118067107557/12500000000000000000)
  directionHi := (435921248944536860457/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree081.table
  base := (1124061678260428930447663193498865324973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1376716191374944010573089255056860000000000000)
      constant := (34805927169322152520623595522719624741176812357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree081.table
  base := (70253850215482100721878598688349421379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-178843570419608097155361739046830000000000000)
      constant := (4563044826857422094633577153596642592091278488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54490156118067107557/12500000000000000000)
  centralHi := (435921248944536860457/100000000000000000000)
  directionLo := (438637295464466792143/100000000000000000000)
  directionHi := (27414830966529174509/6250000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree082.table
  base := (161840067106175553040612091197972803043/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-696610882176752906746464164829760000000000000)
      constant := (17832733390165590268575765156770146306202994935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree082.table
  base := (809200304617423673958462751442189494691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-180988323174181518981362695334560000000000000)
      constant := (4675712724309778905812958696566910188349176819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438637295464466792143/100000000000000000000)
  centralHi := (27414830966529174509/6250000000000000000)
  directionLo := (55167078421968381307/12500000000000000000)
  directionHi := (441336627375747050457/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree083.table
  base := (2125518952135465357753176381146181168341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1409727337332067616412767404262180000000000000)
      constant := (36535533926707290720004016440774022979766164269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree083.table
  base := (2125518901043104763109595960604965955009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-366266151857509881614727303244580000000000000)
      constant := (9579520497096623429754276626818628083816690481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55167078421968381307/12500000000000000000)
  centralHi := (441336627375747050457/100000000000000000000)
  directionLo := (444019549518279726199/100000000000000000000)
  directionHi := (2220097747591398631/500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree084.table
  base := (2645416494224548820288324061323632598827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-203747558615804202761800925552120000000000000)
      constant := (5345161229618178422985151895948052225109294549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree084.table
  base := (2645416452005413107662515720730760900387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-370555657366656725266729215820040000000000000)
      constant := (9810374798861008268853151954015312642392205683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444019549518279726199/100000000000000000000)
  centralHi := (2220097747591398631/500000000000000000)
  directionLo := (111671589394257168763/25000000000000000000)
  directionHi := (446686357577028675053/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree085.table
  base := (794523317815424633409069310321698387843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-721369241644595611126222776733750000000000000)
      constant := (19153625410558423794912474808022218737729244374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree085.table
  base := (3178093236376886121271706374686441396469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-374845162875803568918731128395500000000000000)
      constant := (10043988353639584830586978467787298456775139621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111671589394257168763/25000000000000000000)
  centralHi := (446686357577028675053/100000000000000000000)
  directionLo := (449337338462374150167/100000000000000000000)
  directionHi := (56167167307796768771/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree086.table
  base := (3723549258247254062984437649844972332689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1459244056267753025172284628070160000000000000)
      constant := (39208900567045875599932483111840741464857781001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree086.table
  base := (930887307356115914573651938399016175107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-189567334192475206285366520485480000000000000)
      constant := (5140180580584980039935317123651490325203420326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449337338462374150167/100000000000000000000)
  centralHi := (56167167307796768771/12500000000000000000)
  directionLo := (451972770670388112477/100000000000000000000)
  directionHi := (225986385335194056239/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree087.table
  base := (535223053893292243807137383240440098433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7105000000000000000000000000000000000000000
      center := (14637)
      previous := (0)
      next := (9520)
      square := (234835387906367114713157565485000000000000)
      linear := (-25443959124936462553312477632290000000000000)
      constant := (691742721450411719414776961747603661519493172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree087.table
  base := (1070446101833428440320697795293714313281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-191712086947048628111367476773210000000000000)
      constant := (5259746610599743354033774456367827030299196258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451972770670388112477/100000000000000000000)
  centralHi := (225986385335194056239/50000000000000000000)
  directionLo := (454592924624310783803/100000000000000000000)
  directionHi := (113648231156077695951/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree088.table
  base := (970559753360352796284776619313529757671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1492255202224876631011962777275480000000000000)
      constant := (41043782651396575481479988361409976238919321195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree088.table
  base := (4852798747129731169116584000491611524609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-387713679403244099874736866121880000000000000)
      constant := (10761384533484423945262503856867935506664576881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454592924624310783803/100000000000000000000)
  centralHi := (113648231156077695951/25000000000000000000)
  directionLo := (457198062998413595383/100000000000000000000)
  directionHi := (57149757874801699423/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree089.table
  base := (5436592242859930489617815074786041674669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1508760775203438433931801851878140000000000000)
      constant := (41977014987942793295136061092935587991371434821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree089.table
  base := (1359148056652409088283283695204048810957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-196001592456195471763369389348670000000000000)
      constant := (5503017548894610721267957444435604507670885626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457198062998413595383/100000000000000000000)
  centralHi := (57149757874801699423/12500000000000000000)
  directionLo := (114947110256336595451/25000000000000000000)
  directionHi := (91957688205069276361/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree090.table
  base := (6033164837707424652115939969236388019569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1525266348182000236851640926480800000000000000)
      constant := (42920774852871866038005449922051262313898418921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree090.table
  base := (3016582412142320732418297574497713277063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-198146345210768893589370345636400000000000000)
      constant := (5626722456942952324801544776677346240156361367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114947110256336595451/25000000000000000000)
  centralHi := (91957688205069276361/20000000000000000000)
  directionLo := (28897769174249169071/6250000000000000000)
  directionHi := (462364306787986705137/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree091.table
  base := (664251653041648076232586607159015641561/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (60639)
      previous := (0)
      next := (39440)
      square := (972889464183520903811652771295000000000000)
      linear := (-110126565797183002840820000077390000000000000)
      constant := (3133933017522955815220370641346320625409348035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree091.table
  base := (6642516519330024696599476149793382641143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-400582195930684630830742603848260000000000000)
      constant := (11503613981553544092806907819992287996439886087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28897769174249169071/6250000000000000000)
  centralHi := (462364306787986705137/100000000000000000000)
  directionLo := (464925901496735874987/100000000000000000000)
  directionHi := (116231475374183968747/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree092.table
  base := (7264647300697774620440882149080631348779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1558277494139123842691319075686120000000000000)
      constant := (44839877164455236659425443500136183737251833811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree092.table
  base := (7264647291541659143127717018261123991129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-404871701439831474482744516423720000000000000)
      constant := (11756542300577794189809104998128652264421887561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464925901496735874987/100000000000000000000)
  centralHi := (116231475374183968747/25000000000000000000)
  directionLo := (467473459753138938247/100000000000000000000)
  directionHi := (58434182469142367281/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree093.table
  base := (1579911425771862434698668713349343114229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1574783067117685645611158150288780000000000000)
      constant := (45815219609461944394097469818152235401971314305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree093.table
  base := (7899557121297989731569276927358842490371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-409161206948978318134746428999180000000000000)
      constant := (12012229870750489862841793786629719959980345939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467473459753138938247/100000000000000000000)
  centralHi := (58434182469142367281/12500000000000000000)
  directionLo := (470007209800644091879/100000000000000000000)
  directionHi := (11750180245016102297/2500000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree094.table
  base := (1709449199154079055843534662121351712593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1591288640096247448530997224891440000000000000)
      constant := (46801089579553147677356645769727473913621224685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree094.table
  base := (133550718586352390647592011512836725607/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-206725356229062580893374170787320000000000000)
      constant := (6135338345934645673526380124702209914302869216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470007209800644091879/100000000000000000000)
  centralHi := (11750180245016102297/2500000000000000000)
  directionLo := (236263686881630062253/50000000000000000000)
  directionHi := (472527373763260124507/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree095.table
  base := (575482117676864412225664123336314421819/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-803897106537404625725418149747050000000000000)
      constant := (23898743536981154966386179807436654448069913368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree095.table
  base := (9207713877674298220483657117110037657247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-417740217967272005438750254150100000000000000)
      constant := (12531882763737369327223310630901670389505733423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236263686881630062253/50000000000000000000)
  centralHi := (472527373763260124507/100000000000000000000)
  directionLo := (475034167872818169207/100000000000000000000)
  directionHi := (59379270984102271151/12500000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree096.table
  base := (39523843087750787659344364640597233887/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-812149893026685527185337687048380000000000000)
      constant := (24402206045971775753645446540162736426406172875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree096.table
  base := (1235120095960137700109567891801917192913/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-211014861738209424545376083362780000000000000)
      constant := (6397924043081561975044305332036346157998456068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475034167872818169207/100000000000000000000)
  centralHi := (59379270984102271151/12500000000000000000)
  directionLo := (95505560537099169397/20000000000000000000)
  directionHi := (238763901342747923493/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree097.table
  base := (5283493322735054044884430759942205828149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-820402679515966428645257224349710000000000000)
      constant := (24910932316385304838337681748177743359972192141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree097.table
  base := (10566986641955973962866649528197380568509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-426319228985565692742754079301020000000000000)
      constant := (13062572658959932411440608816880416010451311981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95505560537099169397/20000000000000000000)
  centralHi := (238763901342747923493/50000000000000000000)
  directionLo := (240004241644108717009/50000000000000000000)
  directionHi := (480008483288217434019/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree098.table
  base := (11265791486256508172170540334911842357201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-236758704572927808601479074757440000000000000)
      constant := (7264263527962271857264973538946386015956842287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree098.table
  base := (2253158296671110143695429532726900589541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-430608734494712536394755991876480000000000000)
      constant := (13332056481945920756365458914338018441772202345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240004241644108717009/50000000000000000000)
  centralHi := (480008483288217434019/100000000000000000000)
  directionLo := (482476409495502667549/100000000000000000000)
  directionHi := (9649528189910053351/2000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree099.table
  base := (11977375277559116654437114493837852296491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1673816504989056463130192597904740000000000000)
      constant := (51888352280149684282891393132825694055286097619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree099.table
  base := (2395475055032905055347036411012420417499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-434898240003859380046757904451940000000000000)
      constant := (13604299554943756297239529932598083841046234455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482476409495502667549/100000000000000000000)
  centralHi := (9649528189910053351/2000000000000000000)
  directionLo := (242465888018649459263/50000000000000000000)
  directionHi := (484931776037298918527/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree100.table
  base := (6350869001527104080349705005187253910171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-845161038983809133025015836253700000000000000)
      constant := (26468693692669634561885452893078761546384236739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree100.table
  base := (12701738001077745949986035088142595957297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-439187745513006223698759817027400000000000000)
      constant := (13879301877780457679808492972490104800510963873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242465888018649459263/50000000000000000000)
  centralHi := (484931776037298918527/100000000000000000000)
  directionLo := (97474954547659287143/20000000000000000000)
  directionHi := (121843693184574108929/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree101.table
  base := (13438879646814965312643785433775443117761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1706827650946180068969870747110060000000000000)
      constant := (53996950010648329306150425882076382235439813049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree101.table
  base := (1343887964518374464055237344538780640069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-221738625511076533675380864801430000000000000)
      constant := (7078531725143610069512044602424424619052460105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97474954547659287143/20000000000000000000)
  centralHi := (121843693184574108929/25000000000000000000)
  directionLo := (244902792344596981517/50000000000000000000)
  directionHi := (97961116937838792607/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree102.table
  base := (14188800193295688031907091304185856754763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1723333223924741871889709821712720000000000000)
      constant := (55067040155436242075500686394491114971007028467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree102.table
  base := (14188800191949505013851520608831405664243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-447766756531299911002763642178320000000000000)
      constant := (14437584272299253904592731014495212382691953987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244902792344596981517/50000000000000000000)
  centralHi := (97961116937838792607/20000000000000000000)
  directionLo := (123056098102588007361/25000000000000000000)
  directionHi := (98444878482070405889/20000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree103.table
  base := (14951499627317179048894437402837929861701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1739838796903303674809548896315380000000000000)
      constant := (56147657819077487891538951492376518251670836509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree103.table
  base := (14951499626206310146833284623430956428213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030000000000000000000000000000000000000000
      center := (2142)
      previous := (0)
      next := (1360)
      square := (34043694517038441682554861710000000000000)
      linear := (-4388895747965502472376364609260000000000000)
      constant := (142921013045200330666774552572603388512105939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123056098102588007361/25000000000000000000)
  centralHi := (98444878482070405889/20000000000000000000)
  directionLo := (494631372008243409147/100000000000000000000)
  directionHi := (123657843002060852287/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree104.table
  base := (3931744483513288835973666187681837158003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-878172184940932738864693985459020000000000000)
      constant := (28619401500480545228652972012683401654888291254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree104.table
  base := (15726977933136536102303223921239457330639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-456345767549593598306767467329240000000000000)
      constant := (15006903664199160428929537075703309402820749151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494631372008243409147/100000000000000000000)
  centralHi := (123657843002060852287/25000000000000000000)
  directionLo := (497026695325084467981/100000000000000000000)
  directionHi := (248513347662542233991/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree105.table
  base := (1032202193688597490780969422831701473451/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (60639)
      previous := (0)
      next := (39440)
      square := (972889464183520903811652771295000000000000)
      linear := (-126632138775744805760659074680050000000000000)
      constant := (4167176835749292417659592790335556812593648296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree105.table
  base := (1651523509826127959570841888525929515639/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-230317636529370220979384689952350000000000000)
      constant := (7647851116888113165201091786226982931157070755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497026695325084467981/100000000000000000000)
  centralHi := (248513347662542233991/50000000000000000000)
  directionLo := (499410530082007185069/100000000000000000000)
  directionHi := (49941053008200718507/10000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree106.table
  base := (17316271108052668002592382222492350925081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1789355515838989083569066120123360000000000000)
      constant := (59452675917081072389432158428198167289271662929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree106.table
  base := (541133472107147680177850164981778720403/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-232462389283943642805385646240080000000000000)
      constant := (7793630026118347579615787472674807047116086832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499410530082007185069/100000000000000000000)
  centralHi := (49941053008200718507/10000000000000000000)
  directionLo := (501783040016109417041/100000000000000000000)
  directionHi := (250891520008054708521/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree107.table
  base := (9065042973658950156268817317973113302359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-902930544408775443244452597363010000000000000)
      constant := (30287701825081834822020152167115239026076912031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree107.table
  base := (18130085946803176744490478411790042352003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-469214284077034129262773205055620000000000000)
      constant := (15881577119433783996738633634713650559312399827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501783040016109417041/100000000000000000000)
  centralHi := (250891520008054708521/50000000000000000000)
  directionLo := (504144385011700319241/100000000000000000000)
  directionHi := (252072192505850159621/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree108.table
  base := (9478339801639633009803962635181355434747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-911183330898056344704372134664340000000000000)
      constant := (30854329449590081692858835276007748476110489123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree108.table
  base := (9478339801427336914025548073071667646221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-236751894793090486457387558815540000000000000)
      constant := (8089326717611976755516019318811377322058758589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504144385011700319241/100000000000000000000)
  centralHi := (252072192505850159621/50000000000000000000)
  directionLo := (506494721226038629761/100000000000000000000)
  directionHi := (253247360613019314881/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree109.table
  base := (1237253253918710878464019024183065387369/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-919436117387337246164291671965670000000000000)
      constant := (31426220831792526982963714470883244532384712968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree109.table
  base := (3959210412469831207974884396400938728131/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-477793295095327816566777030206540000000000000)
      constant := (16478488999466803549212115919443417794833708895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506494721226038629761/100000000000000000000)
  centralHi := (253247360613019314881/50000000000000000000)
  directionLo := (101766840241968728911/20000000000000000000)
  directionHi := (127208550302460911139/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree110.table
  base := (5162050828156989268271689716791747170451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-927688903876618147624211209267000000000000000)
      constant := (32003375971422336908785588431442042218294230518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree110.table
  base := (10324101656169553075609894209530411168243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-241041400302237330109389471391000000000000000)
      constant := (8390541906012486950499577869332408132083889987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101766840241968728911/20000000000000000000)
  centralHi := (127208550302460911139/25000000000000000000)
  directionLo := (511162974022842061771/100000000000000000000)
  directionHi := (127790743505710515443/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree111.table
  base := (34421013344628579220671119553099278821/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1871883380731798098168261493136660000000000000)
      constant := (65171589736436816185212732666413322613084118125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree111.table
  base := (21513133340154642076207333964137724343609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-486372306113621503870780855357460000000000000)
      constant := (17086437872764049787344058644705867117561347881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511162974022842061771/100000000000000000000)
  centralHi := (127790743505710515443/25000000000000000000)
  directionLo := (513481185344598355947/100000000000000000000)
  directionHi := (128370296336149588987/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree112.table
  base := (22390842133591467158402787382640858306219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-269769850530051414441157223962760000000000000)
      constant := (9478136434835768775790862940853766732848711253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree112.table
  base := (22390842133395017258822075229285326137839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-490661811622768347522782767932920000000000000)
      constant := (17394551181552471688034061678803808024996333951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513481185344598355947/100000000000000000000)
  centralHi := (128370296336149588987/25000000000000000000)
  directionLo := (515788977580861871627/100000000000000000000)
  directionHi := (128947244395215467907/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree113.table
  base := (4656265936016498203379275556082062495281/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1904894526688921704007939642341980000000000000)
      constant := (67532847864585039484510882622234698566840173645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree113.table
  base := (23281329679920498417959633667499539079293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-494951317131915191174784680508380000000000000)
      constant := (17705423738261449172689928488953472610092219437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (515788977580861871627/100000000000000000000)
  centralHi := (128947244395215467907/25000000000000000000)
  directionLo := (12952162249141258041/2500000000000000000)
  directionHi := (518086489965650321641/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree114.table
  base := (2418459596797816285381780971001760284861/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-960700049833741753463889358472320000000000000)
      constant := (34364634099075453601467926095941797697894184745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree114.table
  base := (12092297983922296493161506399595354722923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-249620411320531017413393296541920000000000000)
      constant := (9009527771382439220832602619751447118255490107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12952162249141258041/2500000000000000000)
  centralHi := (518086489965650321641/100000000000000000000)
  directionLo := (104074771731855353111/20000000000000000000)
  directionHi := (130093464664819191389/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree115.table
  base := (12550320492818364235846482371041540976107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-968952836323022654923808895773650000000000000)
      constant := (34968108022034119768543619174283375862084393363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree115.table
  base := (25100640985526601907932233819836931155161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-503530328150208878478788505659300000000000000)
      constant := (18335446594939263318675000335314900002625103049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104074771731855353111/20000000000000000000)
  centralHi := (130093464664819191389/25000000000000000000)
  directionLo := (130662804210628840447/25000000000000000000)
  directionHi := (522651216842515361789/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree116.table
  base := (3253683090206908498233639095251188374723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7105000000000000000000000000000000000000000
      center := (14637)
      previous := (0)
      next := (9520)
      square := (234835387906367114713157565485000000000000)
      linear := (-33696745614217364013232014933620000000000000)
      constant := (1226787782790812647611006667879167754721925532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree116.table
  base := (26029464721564476260541285429197269340903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-507819833659355722130790418234760000000000000)
      constant := (18654596894663639466703205842505233830437639927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130662804210628840447/25000000000000000000)
  centralHi := (522651216842515361789/100000000000000000000)
  directionLo := (262459347403545085841/50000000000000000000)
  directionHi := (524918694807090171683/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree117.table
  base := (26971067164862805012294693610624387273021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-1970916818603168915687295940752620000000000000)
      constant := (72381694271087244510178916614559190375133922389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree117.table
  base := (26971067164787958536042854842278748676043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-512109339168502565782792330810220000000000000)
      constant := (18976506441819501623846311279737905244704140187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262459347403545085841/50000000000000000000)
  centralHi := (524918694807090171683/100000000000000000000)
  directionLo := (263588210021330494711/50000000000000000000)
  directionHi := (527176420042660989423/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree118.table
  base := (6981362076078422234025094414356458067973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-993711195790865359303567507677640000000000000)
      constant := (36810112325638756533560338888262890561046198714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree118.table
  base := (2792544830425199141975551393969498475701/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-258199422338824704717397121692840000000000000)
      constant := (9650587618145366838526430688047172046643559545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263588210021330494711/50000000000000000000)
  centralHi := (527176420042660989423/100000000000000000000)
  directionLo := (529424517320470526339/100000000000000000000)
  directionHi := (26471225866023526317/5000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree119.table
  base := (28892608129281233843658646564801213310587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-286275423508613217360996298565420000000000000)
      constant := (10695611791713700461778427688530974742759425669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree119.table
  base := (7223152032307594655091370429304551062351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-260344175093398126543398077980570000000000000)
      constant := (9814301638981770704934154114450348964440963518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529424517320470526339/100000000000000000000)
  centralHi := (26471225866023526317/5000000000000000000)
  directionLo := (132915777193452061171/25000000000000000000)
  directionHi := (106332621754761648937/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree120.table
  base := (14936273314625799666755672147951561336017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1010216768769427162223406582280300000000000000)
      constant := (38064433971404575078530087796004935891095924553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree120.table
  base := (29872546629209683767062967285619349103543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-524977855695943096738798068536600000000000000)
      constant := (19958790566726387775834730766613135674639487687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132915777193452061171/25000000000000000000)
  centralHi := (106332621754761648937/20000000000000000000)
  directionLo := (53389231397543767067/10000000000000000000)
  directionHi := (533892313975437670671/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree121.table
  base := (30865263793917899820764353426539676145137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2036939110517416127366652239163260000000000000)
      constant := (77398980853292517392886321408471403514264950633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree121.table
  base := (7716315948470838662683414530729470621881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-264633680602544970195399990556030000000000000)
      constant := (10145868551234965281282817623842982907655071058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53389231397543767067/10000000000000000000)
  centralHi := (533892313975437670671/100000000000000000000)
  directionLo := (268056125006063039643/50000000000000000000)
  directionHi := (536112250012126079287/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree122.table
  base := (6374151922634906030892571123174248897879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2053444683495977930286491313765920000000000000)
      constant := (78679621273029563057261734160093758114163478555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree122.table
  base := (6374151922629212235225421848281312325253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-533556866714236784042801893687520000000000000)
      constant := (20627442885086962323080509701244602212293045385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268056125006063039643/50000000000000000000)
  centralHi := (536112250012126079287/100000000000000000000)
  directionLo := (538323031556407997131/100000000000000000000)
  directionHi := (134580757889101999283/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree123.table
  base := (822225851927792410258150933090051620369/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1034975128237269866603165194184290000000000000)
      constant := (39985394600805957226180362900847443744475722420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree123.table
  base := (32889034077088236339819005953891200294929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-537846372223383627694803806262980000000000000)
      constant := (20965907914472352461040025572772601743928901761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538323031556407997131/100000000000000000000)
  centralHi := (134580757889101999283/25000000000000000000)
  directionLo := (270262385467853490043/50000000000000000000)
  directionHi := (540524770935706980087/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree124.table
  base := (33920087176010141628563326802034925973653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2086455829453101536126169462971240000000000000)
      constant := (81272484638639050718127286662123937264448266477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree124.table
  base := (16960043587995405188801915806647568115323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-271067938866265235673402859419220000000000000)
      constant := (10653566095261495682657863268080564050135461707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270262385467853490043/50000000000000000000)
  centralHi := (540524770935706980087/100000000000000000000)
  directionLo := (108543515639786711721/20000000000000000000)
  directionHi := (271358789099466779303/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree125.table
  base := (17481959450168028530092383271404544596093/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1051480701215831669523004268786950000000000000)
      constant := (41292353791859046564912144791209434878260396437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree125.table
  base := (8740979725080032238431135703760668980103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-273212691620838657499403815706950000000000000)
      constant := (10825557856568868248529783058965518874419825454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108543515639786711721/20000000000000000000)
  centralHi := (271358789099466779303/50000000000000000000)
  directionLo := (54490156118067107557/10000000000000000000)
  directionHi := (544901561180671075571/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree126.table
  base := (7204105848147234036656091993367839674477/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-302780996487175020280835373168080000000000000)
      constant := (11986779719494800382870907090636022360818230495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree126.table
  base := (2251283077545190431796156003745180012531/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-275357444375412079325404771994680000000000000)
      constant := (10998929241108680169637508656599600918023531032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54490156118067107557/10000000000000000000)
  centralHi := (544901561180671075571/100000000000000000000)
  directionLo := (547076825563055343199/100000000000000000000)
  directionHi := (683846031953819179/125000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree127.table
  base := (18544959094016500684040836019428432529789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1067986274194393472442843343389610000000000000)
      constant := (42620367998248692305440163508077711276120074901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree127.table
  base := (18544959094011094827895649386760124294477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-277502197129985501151405728282410000000000000)
      constant := (11173680248832250062485070935571823158640106493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547076825563055343199/100000000000000000000)
  centralHi := (683846031953819179/125000000000000000)
  directionLo := (137310868733862147887/25000000000000000000)
  directionHi := (549243474935448591549/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree128.table
  base := (38172085733220281618551530195853744553693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2152478121367348747805525761381880000000000000)
      constant := (86584541463448299583118538246079656959313134837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree128.table
  base := (19086042866605687413667380465468765633131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-279646949884558922977406684570140000000000000)
      constant := (11349810879691804632703810521895118134601886779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137310868733862147887/25000000000000000000)
  centralHi := (549243474935448591549/100000000000000000000)
  directionLo := (551401610852003048627/100000000000000000000)
  directionHi := (137850402713000762157/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree129.table
  base := (9816757966864631077247519523525893501501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1084491847172955275362682417992270000000000000)
      constant := (43969437218476040596226256911628122090606709418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree129.table
  base := (19633515933725593617376722206850383275183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-281791702639132344803407640857870000000000000)
      constant := (11527321133640455202425716824070040716166416447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551401610852003048627/100000000000000000000)
  centralHi := (137850402713000762157/25000000000000000000)
  directionLo := (553551332887204659821/100000000000000000000)
  directionHi := (276775666443602329911/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree130.table
  base := (20187378291035372137580111132856287650387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1092744633662236176822601955293600000000000000)
      constant := (44651867458325579778624603681483374757784797883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree130.table
  base := (1009368914551617515483454822928486615359/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-283936455393705766629408597145600000000000000)
      constant := (11706211010632175016311467122478466290046872620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553551332887204659821/100000000000000000000)
  centralHi := (276775666443602329911/50000000000000000000)
  directionLo := (555692738689482902419/100000000000000000000)
  directionHi := (27784636934474145121/5000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree131.table
  base := (20747629934269159008898729627096454960141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1100997420151517078282521492594930000000000000)
      constant := (45339561451097245360863713971136382812452450469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree131.table
  base := (8299051973706668010140543814601381671659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-572162416296558376910819106866660000000000000)
      constant := (23772961021243554587285654711551060290773151655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555692738689482902419/100000000000000000000)
  centralHi := (27784636934474145121/5000000000000000000)
  directionLo := (278912962016484180627/50000000000000000000)
  directionHi := (111565184806593672251/20000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree132.table
  base := (4262854171849697913792982130873397528833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1109250206640797979742441029896260000000000000)
      constant := (46032519196618695815925969871065569193828395485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree132.table
  base := (8525708343698575834639944873721825640247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-576451921805705220562821019442120000000000000)
      constant := (24136259267129787991432532858001294241086902115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278912962016484180627/50000000000000000000)
  centralHi := (111565184806593672251/20000000000000000000)
  directionLo := (559950982867475686821/100000000000000000000)
  directionHi := (279975491433737843411/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree133.table
  base := (43774602123732943453122935805274000942361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-319286569465736823200674447770740000000000000)
      constant := (13351640198491625779321257814439558043547679207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree133.table
  base := (43774602123729566816450472746910491147683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-580741427314852064214822932017580000000000000)
      constant := (24502316758835910558897020673478543400585768947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (559950982867475686821/100000000000000000000)
  centralHi := (279975491433737843411/50000000000000000000)
  directionLo := (281034003683392870997/50000000000000000000)
  directionHi := (112413601473357148399/20000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree134.table
  base := (44933441076179158545693286727877214590919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2251511559238719565324560208997840000000000000)
      constant := (94868451890474022028837702807609372136077181071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree134.table
  base := (22466720538088188888177783430684637827161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-292515466411999453933412422296520000000000000)
      constant := (12435566748138169609644413825766673322708351049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281034003683392870997/50000000000000000000)
  centralHi := (112413601473357148399/20000000000000000000)
  directionLo := (22567083519011885719/4000000000000000000)
  directionHi := (8815266999614017859/1562500000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree135.table
  base := (46105058567911672771560741087394248705871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2268017132217281368244399283600500000000000000)
      constant := (96285949896008778229317735861378679594920238039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree135.table
  base := (46105058567909382840938675464866471959287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-589320438333145751518826757168500000000000000)
      constant := (25242709479367009007598096893965018401016075783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22567083519011885719/4000000000000000000)
  centralHi := (8815266999614017859/1562500000000000000)
  directionLo := (141569578363278500191/25000000000000000000)
  directionHi := (113255662690622800153/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree136.table
  base := (47289454591146119014654863236427056656991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2284522705195843171164238358203160000000000000)
      constant := (97713975405724863072202757279791202577777942119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree136.table
  base := (47289454591144233383652396012453310570389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-593609943842292595170828669743960000000000000)
      constant := (25617044708025335769245787007174197171841256901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141569578363278500191/25000000000000000000)
  centralHi := (113255662690622800153/20000000000000000000)
  directionLo := (568371770919633458611/100000000000000000000)
  directionHi := (142092942729908364653/25000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree137.table
  base := (1939465165529372348364736169241343578887/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2301028278174404974084077432805820000000000000)
      constant := (99152528419307102354882355691116033188558859575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree137.table
  base := (9697325827646551215504969039907175035547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-597899449351439438822830582319420000000000000)
      constant := (25994139182170180033406053281182446099760590615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (568371770919633458611/100000000000000000000)
  centralHi := (142092942729908364653/25000000000000000000)
  directionLo := (570457545895693586867/100000000000000000000)
  directionHi := (142614386473923396717/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree138.table
  base := (49696582201660931872064977382750456212187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2317533851152966777003916507408480000000000000)
      constant := (100601608936445797668271765986308283550048014083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree138.table
  base := (24848291100829826749302713047686387694477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-301094477430293141237416247447440000000000000)
      constant := (13186996450860906004854101916575764887050706493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570457545895693586867/100000000000000000000)
  centralHi := (142614386473923396717/25000000000000000000)
  directionLo := (572535722344339328353/100000000000000000000)
  directionHi := (286267861172169664177/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree139.table
  base := (6364914221755044886890579837571523565271/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1167019712065764289961877791005570000000000000)
      constant := (51030608478418297305040735571721304658405010556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree139.table
  base := (12729828443509826647039432725738445564623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-303239230184866563063417203735170000000000000)
      constant := (13378302933300938832779052056381483337990170814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (572535722344339328353/100000000000000000000)
  centralHi := (286267861172169664177/50000000000000000000)
  directionLo := (114921276542052294947/20000000000000000000)
  directionHi := (35912898919391342171/6250000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree140.table
  base := (6519352981014192704374160747014266926351/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (60639)
      previous := (0)
      next := (39440)
      square := (972889464183520903811652771295000000000000)
      linear := (-167896071222149313060256761186700000000000000)
      constant := (7395096605727168217189189458186691957581713348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree140.table
  base := (26077411924056337565662264086275179321553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-305383982939439984889418160022900000000000000)
      constant := (13570989038366682921658166875783293377422355777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114921276542052294947/20000000000000000000)
  centralHi := (35912898919391342171/6250000000000000000)
  directionLo := (28833480397898054393/5000000000000000000)
  directionHi := (576669607957961087861/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree141.table
  base := (53403112416745005922998901967296532758979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2367050570088652185763433731216460000000000000)
      constant := (105012015506183033229681904641292652818464765611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree141.table
  base := (53403112416744292586727661530247494436177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-615057471388026813430838232621260000000000000)
      constant := (27530109532040576378445411888591525668473401793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28833480397898054393/5000000000000000000)
  centralHi := (576669607957961087861/100000000000000000000)
  directionLo := (144681369402172337673/25000000000000000000)
  directionHi := (578725477608689350693/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree142.table
  base := (6833022434114992372805590281532215561763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1191778071533606994341636402909560000000000000)
      constant := (53251603017277777874612265429209504284338765868) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree142.table
  base := (5466417947291935176768707323319279656799/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-309673488448586828541420072598360000000000000)
      constant := (13960500116224544590750924895621931189394902955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144681369402172337673/25000000000000000000)
  centralHi := (578725477608689350693/100000000000000000000)
  directionLo := (290387034888105266113/50000000000000000000)
  directionHi := (580774069776210532227/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree143.table
  base := (55938025009741361401184048904763048672199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2400061716045775791603111880421780000000000000)
      constant := (108004924065013704974681377791150550472732648591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree143.table
  base := (6992253126217609754044102118238631309353/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-311818241203160250367421028886090000000000000)
      constant := (14157325088942867124255130689425259558243703908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290387034888105266113/50000000000000000000)
  centralHi := (580774069776210532227/100000000000000000000)
  directionLo := (582815461201433571741/100000000000000000000)
  directionHi := (291407730600716785871/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree144.table
  base := (28612324510213692328187513281891218075193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1208283644512168797261475477512220000000000000)
      constant := (54758584798639003030957327710957295205660628337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree144.table
  base := (7153081127553373348477057815033960715591/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-313962993957733672193421985173820000000000000)
      constant := (14355529684139281282912240557985021156926819676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (582815461201433571741/100000000000000000000)
  centralHi := (291407730600716785871/50000000000000000000)
  directionLo := (292424863642977861429/50000000000000000000)
  directionHi := (584849727285955722859/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree145.table
  base := (14631012874577137432354883743198353074489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7105000000000000000000000000000000000000000
      center := (14637)
      previous := (0)
      next := (9520)
      square := (234835387906367114713157565485000000000000)
      linear := (-41949532103498265473151552234950000000000000)
      constant := (1914481769501269263348740582983794719437697738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree145.table
  base := (58524051498308222252903601582837563079291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-632215493424614188038845882923100000000000000)
      constant := (29110227803556817877062029704168573706708198219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292424863642977861429/50000000000000000000)
  centralHi := (584849727285955722859/100000000000000000000)
  directionLo := (586876942124559740283/100000000000000000000)
  directionHi := (146719235531139935071/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree146.table
  base := (1869882263650788877573914886431898617701/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1224789217490730600181314552114880000000000000)
      constant := (56286621583065111769270898362974493762189448144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree146.table
  base := (14959058109206243639112925023381612538087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-318252499466880515845423897749280000000000000)
      constant := (14756077741825454640549871909907451054833129966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586876942124559740283/100000000000000000000)
  centralHi := (146719235531139935071/25000000000000000000)
  directionLo := (58889717853670423571/10000000000000000000)
  directionHi := (588897178536704235711/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree147.table
  base := (61161191829525194193149727275384775541471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-352297715422860429040352596976060000000000000)
      constant := (16302438743168847587898358518715700173612639777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree147.table
  base := (30580595914762486186504812124682226322483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-320397252221453937671424854037010000000000000)
      constant := (14958421204246192315722956192196638739055222147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58889717853670423571/10000000000000000000)
  centralHi := (588897178536704235711/100000000000000000000)
  directionLo := (295455254048522534027/50000000000000000000)
  directionHi := (118182101619409013611/20000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree148.table
  base := (6249892967006103096649302646783192888123/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1241294790469292403101153626717540000000000000)
      constant := (57835713369483588635709852363332602978633303535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree148.table
  base := (3124946483503042420826259747724485620831/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-322542004976027359497425810324740000000000000)
      constant := (15162144289006952354281403914937850679513960790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295455254048522534027/50000000000000000000)
  centralHi := (118182101619409013611/20000000000000000000)
  directionLo := (59291700116502396167/10000000000000000000)
  directionHi := (592917001165023961671/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree149.table
  base := (1276988919043758509009852136099340519829/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1249547576958573304561073164018870000000000000)
      constant := (58618154888114306425328214561858508087040831525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree149.table
  base := (31924722976093887612587055362173667793159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-324686757730600781323426766612470000000000000)
      constant := (15367246996074609068953968070906265441617623831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59291700116502396167/10000000000000000000)
  centralHi := (592917001165023961671/100000000000000000000)
  directionLo := (118983345382711791847/20000000000000000000)
  directionHi := (148729181728389739809/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree150.table
  base := (1630318516744032309911150852624725879399/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1257800363447854206020992701320200000000000000)
      constant := (59405860156856513819742452105983746575283067820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree150.table
  base := (2037898145930036524294179056887478725953/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-326831510485174203149427722900200000000000000)
      constant := (15573729325416568513798375716999808188858166032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118983345382711791847/20000000000000000000)
  centralHi := (148729181728389739809/25000000000000000000)
  directionLo := (596909753356869808731/100000000000000000000)
  directionHi := (149227438339217452183/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree151.table
  base := (16647203454183639825378285864219265212203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1266053149937135107480912238621530000000000000)
      constant := (60198829175585624215817794817799188400259346854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree151.table
  base := (8323601727091807197622680650810921713389/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-328976263239747624975428679187930000000000000)
      constant := (15781591277000756650333919854195177273829375604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (596909753356869808731/100000000000000000000)
  centralHi := (149227438339217452183/25000000000000000000)
  directionLo := (149724036844367488003/25000000000000000000)
  directionHi := (598896147377469952013/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree152.table
  base := (33988832693578499335437554525418451801063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1274305936426416008940831775922860000000000000)
      constant := (60997061944179025848887248200906928980270005167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree152.table
  base := (1359553307743138299464680961276098787601/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-331121015994321046801429635475660000000000000)
      constant := (15990832850795607848978609581313013300941475225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149724036844367488003/25000000000000000000)
  centralHi := (598896147377469952013/100000000000000000000)
  directionLo := (150218993688088855359/25000000000000000000)
  directionHi := (600875974752355421437/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree153.table
  base := (34689647687585810664180233526989885092091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1282558722915696910400751313224190000000000000)
      constant := (61800558462516038385470387328762211174759978019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree153.table
  base := (69379295375171552463231756321512534773131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-666531537497788937254861183526780000000000000)
      constant := (32402908093540107428564509648717096481408146779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150218993688088855359/25000000000000000000)
  centralHi := (600875974752355421437/100000000000000000000)
  directionLo := (301424650089209828567/50000000000000000000)
  directionHi := (120569860035683931427/20000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree154.table
  base := (70793703775013128692384121735714393217423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 58870000000000000000000000000000000000000000
      center := (121278)
      previous := (0)
      next := (78880)
      square := (1945778928367041807623305542590000000000000)
      linear := (-368803288401422231960191671578720000000000000)
      constant := (17888376780136534494555126313252590632870969201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree154.table
  base := (35396851887506536016797473325427577444529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-335410521503467890453431548051120000000000000)
      constant := (16413454864893512222911665371384401169109008161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301424650089209828567/50000000000000000000)
  centralHi := (120569860035683931427/20000000000000000000)
  directionLo := (120963237459424405377/20000000000000000000)
  directionHi := (302408093648561013443/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree155.table
  base := (72220890581005922017741466665290096292777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2598128591788517426641180775653700000000000000)
      constant := (126846685495895160021918688381140189578129047393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree155.table
  base := (18055222645251468850912546406365764796613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-337555274258041312279432504338850000000000000)
      constant := (16626835305135877163787008994780393797454534634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120963237459424405377/20000000000000000000)
  centralHi := (302408093648561013443/50000000000000000000)
  directionLo := (151694174679609164949/25000000000000000000)
  directionHi := (606776698718436659797/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree156.table
  base := (73660855787562166683559966749259641321139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2614634164767079229561019850256360000000000000)
      constant := (128485261029620063374147650923974720559202817051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree156.table
  base := (73660855787562128334971212430010789627403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-679400054025229468210866921253160000000000000)
      constant := (33683190734935015740381107188103264467157118427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151694174679609164949/25000000000000000000)
  centralHi := (606776698718436659797/100000000000000000000)
  directionLo := (608730896044107090801/100000000000000000000)
  directionHi := (304365448022053545401/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree157.table
  base := (37556799694589954841880685238588045824967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1315569868872820516240429462429510000000000000)
      constant := (65067182030951860768572646577388859780401065103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree157.table
  base := (7511359938917987813633020970599784505821/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-341844779767188155931434416914310000000000000)
      constant := (17057735051859219234071681212019950569111274945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608730896044107090801/100000000000000000000)
  centralHi := (304365448022053545401/50000000000000000000)
  directionLo := (122135767978046230451/20000000000000000000)
  directionHi := (4770928436642430877/781250000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree158.table
  base := (38289560690220624274464985026004640333101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1323822655362101417700348999730840000000000000)
      constant := (65896997296261434084024731585470685223486759109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree158.table
  base := (38289560690220611298750284827105972293479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-343989532521761577757435373202040000000000000)
      constant := (17275254358282271993156244807614427260061518711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122135767978046230451/20000000000000000000)
  centralHi := (4770928436642430877/781250000000000000)
  directionLo := (306310294954599769399/50000000000000000000)
  directionHi := (612620589909199538799/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree159.table
  base := (78057421756010549997716274870044048828823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2664150883702764638320537074064340000000000000)
      constant := (133464152621257627154969029814177175208186967007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree159.table
  base := (39028710878005264325245178362984056452119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-346134285276334999583436329489770000000000000)
      constant := (17494153286708363281835081158717062854900530471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306310294954599769399/50000000000000000000)
  centralHi := (612620589909199538799/100000000000000000000)
  directionLo := (614556204811010509389/100000000000000000000)
  directionHi := (61455620481101050939/10000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree160.table
  base := (19887125127658179170500074807835588961587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1340328228340663220620188074333500000000000000)
      constant := (67572419073945720595642658296888193571036077366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree160.table
  base := (7954850051063269912280139536919343079379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-348279038030908421409437285777500000000000000)
      constant := (17714431837109617437156673693111886553645659055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614556204811010509389/100000000000000000000)
  centralHi := (61455620481101050939/10000000000000000000)
  directionLo := (308242871191991136757/50000000000000000000)
  directionHi := (123297148476796454703/20000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree161.table
  base := (810523576391315004531718727448599796413/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (60639)
      previous := (0)
      next := (39440)
      square := (972889464183520903811652771295000000000000)
      linear := (-192654430689992017440015373090690000000000000)
      constant := (9774003655157928733360160499863890350074166550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree161.table
  base := (81052357639131486010376903078785511897987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-700847581570963686470876484130460000000000000)
      constant := (35872180018917154103167006416001165495725744083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308242871191991136757/50000000000000000000)
  centralHi := (123297148476796454703/20000000000000000000)
  directionLo := (618409259514883734521/100000000000000000000)
  directionHi := (309204629757441867261/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree162.table
  base := (82568993136407860637199318285183624224567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2713667602638450047080054297872320000000000000)
      constant := (138537791694006184015103649644470251970670181503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree162.table
  base := (3302759725456313950326430640995750818701/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-705137087080110530122878396705920000000000000)
      constant := (36318255607456388528982549095145418010889972725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618409259514883734521/100000000000000000000)
  centralHi := (309204629757441867261/50000000000000000000)
  directionLo := (310163406104251714853/50000000000000000000)
  directionHi := (620326812208503429707/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree163.table
  base := (21024601749359591465953023135994290975833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1365086587808505924999946686237490000000000000)
      constant := (70125029856534987926066022856855262473646204194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree163.table
  base := (84098406997438356093801492208912834165709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-709426592589257373774880309281380000000000000)
      constant := (36767090439783644569391598445043326257664006781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310163406104251714853/50000000000000000000)
  centralHi := (620326812208503429707/100000000000000000000)
  directionLo := (7777980695083446399/1250000000000000000)
  directionHi := (622238455606675711921/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree164.table
  base := (42820299608636819025121019023268159138137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 206045000000000000000000000000000000000000000
      center := (424473)
      previous := (0)
      next := (276080)
      square := (6810226249284646326681569399065000000000000)
      linear := (-1373339374297786826459866223538820000000000000)
      constant := (70986427614599209428357321102220097569923487633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree164.table
  base := (85640599217273630015116407643609543936409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-713716098098404217426882221856840000000000000)
      constant := (37218684515846414273168998477364333651621363081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7777980695083446399/1250000000000000000)
  centralHi := (622238455606675711921/100000000000000000000)
  directionLo := (124828848801356491833/20000000000000000000)
  directionHi := (312072122003391229583/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree165.table
  base := (87195569791036837192688082624104834942619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2763184321574135455839571521680300000000000000)
      constant := (143706178242190543329134800733656986143150386371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree165.table
  base := (87195569791036830584621746903070077107199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-718005603607551061078884134432300000000000000)
      constant := (37673037835592959245417983924704920448030274191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124828848801356491833/20000000000000000000)
  centralHi := (312072122003391229583/50000000000000000000)
  directionLo := (626044230879747874929/100000000000000000000)
  directionHi := (62604423087974787493/10000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree166.table
  base := (88763318713922185669102870902157108190493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2779689894552697258759410596282960000000000000)
      constant := (145450028751848307979365571833732072271422026037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree166.table
  base := (44381659356961090117421565546222218773699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-361147554558348952365443023503880000000000000)
      constant := (19065075199486147495962609550684811518970172691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626044230879747874929/100000000000000000000)
  centralHi := (62604423087974787493/10000000000000000000)
  directionLo := (627938468887543251197/100000000000000000000)
  directionHi := (313969234443771625599/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree167.table
  base := (90343845981193530805170363914538437516411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2796195467531259061679249670885620000000000000)
      constant := (147204406757976540691851065854909184471613780899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree167.table
  base := (18068769196238705267274207092725824976963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-726584614625844748382887959583220000000000000)
      constant := (38590022205934175669445298359305811385903002335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627938468887543251197/100000000000000000000)
  centralHi := (313969234443771625599/50000000000000000000)
  directionLo := (629827009900217906377/100000000000000000000)
  directionHi := (314913504950108953189/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree168.table
  base := (22984287897045736125386561320947835928867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 29435000000000000000000000000000000000000000
      center := (60639)
      previous := (0)
      next := (39440)
      square := (972889464183520903811652771295000000000000)
      linear := (-200907217179272918899934910392020000000000000)
      constant := (10640665161455920058396100204542119820226480058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree168.table
  base := (22984287897045735206702951631233274565691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (110313)
      previous := (0)
      next := (70040)
      square := (1753250267627479746651575378065000000000000)
      linear := (-365437060067495796017444936079340000000000000)
      constant := (19526326628214539614582143714310067619734831638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell230.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629827009900217906377/100000000000000000000)
  centralHi := (314913504950108953189/50000000000000000000)
  directionLo := (631709905012471880301/100000000000000000000)
  directionHi := (315854952506235940151/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 123
  qDenominator := 203
  table := BinomialMassData.Q123_203.Degree169.table
  base := (93543235530289358764677347984741720833357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 412090000000000000000000000000000000000000000
      center := (848946)
      previous := (0)
      next := (552160)
      square := (13620452498569292653363138798130000000000000)
      linear := (-2829206613488382667518927820090940000000000000)
      constant := (150744745258877722945502250399833151573821808613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q123_203.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree169.table
  base := (93543235530289355743015284729994247466971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (220626)
      previous := (0)
      next := (140080)
      square := (3506500535254959493303150756130000000000000)
      linear := (-735163625644138435686891784734140000000000000)
      constant := (39518043550408192941061126266685238971377095339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell230.Kernel169
