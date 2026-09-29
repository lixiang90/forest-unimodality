import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell172.Parameters
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch000_049
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch050_099
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch100_149
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch150_199
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch000_049
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch050_099
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch100_149
import ForestUnimodality.BinomialMassData.Q31883_60208.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree000.table
  base := (135861420160022380845248337/2000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (187982309815466833158303927500000000000)
      linear := (-14732509843415244731729130000000000000)
      constant := (169826775200027976056560421250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree000.table
  base := (135861420160022380845248337/2000000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (34)
      previous := (17)
      next := (17)
      square := (187982309815466833158303927500000000000)
      linear := (-14732509843415244731729130000000000000)
      constant := (169826775200027976056560421250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree001.table
  base := (380321459323160512996596379076494565793843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-108973523163140606955001125460047990000000000000)
      constant := (48499579002552479118344782791515913080501924355203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree001.table
  base := (11882613629157718062554127403680306612761/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-3027779161578734500513754906194925937500000000)
      constant := (1346935449488755085871949526777006142725528407872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49912617763438063261/100000000000000000000)
  directionHi := (24956308881719031631/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree002.table
  base := (113554306277051750504885326196391571189933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-105218456237955985708603530885634530000000000000)
      constant := (14529225089337473054726603965387312659024841408093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree002.table
  base := (56757295031632129592592433796786189852117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-5846943493980545598449865669366881875000000000)
      constant := (806899595816282023425449289439923319351749227773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49912617763438063261/100000000000000000000)
  centralHi := (24956308881719031631/50000000000000000000)
  directionLo := (70587100974598367371/100000000000000000000)
  directionHi := (17646775243649591843/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree003.table
  base := (145460641673874466709949398403078705753561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-34655589087631481764379222009165570000000000000)
      constant := (2087930403987514778206000032756318581271696111809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree003.table
  base := (145397595842648942528979177392049865404957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-34664431305529426785543905730155351250000000000)
      constant := (2087052056142029154522935078731621114428632057733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70587100974598367371/100000000000000000000)
  centralHi := (17646775243649591843/25000000000000000000)
  directionLo := (5403199369064974217/6250000000000000000)
  directionHi := (86451189905039587473/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree004.table
  base := (19920468467193465418005207868012017043391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-413363691101454700341618934393711200000000000000)
      constant := (13139102918185993547369243803840444731438360188555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree004.table
  base := (99555668078727191668720413523475993490933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-45941088635136671177288348782843175000000000000)
      constant := (1459264840262390480119098917537927192149511247677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5403199369064974217/6250000000000000000)
  centralHi := (86451189905039587473/100000000000000000000)
  directionLo := (49912617763438063261/50000000000000000000)
  directionHi := (99825235526876126523/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree005.table
  base := (36072875256204922791395768208492195664781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-257413540207113032401912435352466135000000000000)
      constant := (4942844721375979683050999914972424675899296771901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree005.table
  base := (72111411845965960462098914754427215655083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-57217745964743915569032791835530998750000000000)
      constant := (1097963288939379120308365799412977407617608489027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49912617763438063261/50000000000000000000)
  centralHi := (99825235526876126523/100000000000000000000)
  directionLo := (2790200156350275669/2500000000000000000)
  directionHi := (111608006254011026761/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree006.table
  base := (54529746828915923155407683847677023338251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-68476718858555269918447867446239260000000000000)
      constant := (882232348340437967794526497868776577886578324419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree006.table
  base := (54503918160071256253274116942207237764389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-68494403294351159960777234888218822500000000000)
      constant := (881923484161773793399274499040852120235680421741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2790200156350275669/2500000000000000000)
  centralHi := (111608006254011026761/100000000000000000000)
  directionLo := (122260445246998987667/100000000000000000000)
  directionHi := (30565111311749746917/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree007.table
  base := (42454619713972635644625183520046159359689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-717753859039768793728236743327374410000000000000)
      constant := (6754346212587033252993316902875454006507152246969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree007.table
  base := (42434560130260276353408234513775271716267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-79771060623958404352521677940906646250000000000)
      constant := (750276142688145471024227559121531926577948269123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122260445246998987667/100000000000000000000)
  centralHi := (30565111311749746917/25000000000000000000)
  directionLo := (33014093471570507299/25000000000000000000)
  directionHi := (132056373886282029197/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree008.table
  base := (16848165510696769878724503909737716831507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-409608624176270079095221339819297740000000000000)
      constant := (3022509935604606655895100065735266144074552802147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree008.table
  base := (6736053749454522660497092871119531008883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-91047717953565648744266120993594470000000000000)
      constant := (671542231648704218540540464896653978932618906135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33014093471570507299/25000000000000000000)
  centralHi := (132056373886282029197/100000000000000000000)
  directionLo := (141174201949196734743/100000000000000000000)
  directionHi := (17646775243649591843/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree009.table
  base := (27056287408478526121635328367872421708077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-102297848629479058072516512883312950000000000000)
      constant := (628817950252922855697364388359684709325638985013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree009.table
  base := (5408623817163003100121826990289631314101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-102324375283172893136010564046282293750000000000)
      constant := (628758931651985218734155965158968601581498715345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141174201949196734743/100000000000000000000)
  centralHi := (17646775243649591843/12500000000000000000)
  directionLo := (18717231661289273723/12500000000000000000)
  directionHi := (29947570658062837957/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree010.table
  base := (1092679021940301653170600802380889702319/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-255536006744520721778713638065259405000000000000)
      constant := (1377648812247253701137682263004387262483852935995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree010.table
  base := (2730326992630430944767767096592116125123/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-28400258153195034381938751774742529375000000000)
      constant := (153072578898426827961457935078033306290921151574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18717231661289273723/12500000000000000000)
  centralHi := (29947570658062837957/20000000000000000000)
  directionLo := (78918778056921802741/50000000000000000000)
  directionHi := (157837556113843605483/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree011.table
  base := (17677063451028655574411074155169180003289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-1123607416290854251577060488572258690000000000000)
      constant := (5546323805471155417944113574189266479441935162569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree011.table
  base := (8833927139046113460423067292349131158547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-62438844971193690959749725075828970625000000000)
      constant := (308158949368610770303600648576605360204285064443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78918778056921802741/50000000000000000000)
  centralHi := (157837556113843605483/100000000000000000000)
  directionLo := (20692678178218996633/12500000000000000000)
  directionHi := (33108285085150394613/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree012.table
  base := (3565603160335875925942886216492294393777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-34029744600100711556646289580096660000000000000)
      constant := (159246149836932823942308259363163005813634868313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree012.table
  base := (14254648361911997744606638238219215508877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-136154347271994626311243893204345765000000000000)
      constant := (637100766426839802924465799821926642528119320213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20692678178218996633/12500000000000000000)
  centralHi := (33108285085150394613/20000000000000000000)
  directionLo := (34580475962015834989/20000000000000000000)
  directionHi := (86451189905039587473/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree013.table
  base := (5714857903535151389561104759161961410207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-663267097458198490250736180597350415000000000000)
      constant := (3023639865104129527771457778900751891210085004847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree013.table
  base := (5711582755691817660626557746236545714111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-73715502300800935351494168128516794375000000000)
      constant := (336046228753096091898927415484113130096631194759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34580475962015834989/20000000000000000000)
  centralHi := (86451189905039587473/50000000000000000000)
  directionLo := (179962502638710677609/100000000000000000000)
  directionHi := (17996250263871067761/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree014.table
  base := (2262673138060386345041820508525268825629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-356999396057292086240919574376480475000000000000)
      constant := (1618307641232651546645571747171090723572043541709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree014.table
  base := (9045173169635349792778205641081688130167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-158707661931209115094732779309721412500000000000)
      constant := (719477177298672027505498159745834855947208718223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179962502638710677609/100000000000000000000)
  centralHi := (17996250263871067761/10000000000000000000)
  directionLo := (37351182989558454141/20000000000000000000)
  directionHi := (93377957473896135353/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree015.table
  base := (7030667727902397477557474458037991097713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-169940108171326634380653803757460330000000000000)
      constant := (777627594812546382893153303604088249864111593497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree015.table
  base := (1756506835819577192902337663919912817457/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-42496079815204089871619305590602309062500000000)
      constant := (194478687715764646181673716177698054630379145233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37351182989558454141/20000000000000000000)
  centralHi := (93377957473896135353/50000000000000000000)
  directionLo := (193310737363412106421/100000000000000000000)
  directionHi := (96655368681706053211/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree016.table
  base := (5298079696760355974659829235297663483943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-1630924362854711073888090170128364040000000000000)
      constant := (7614413171453385917379079699541928802139854997303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree016.table
  base := (2647094407630418209122130111774009445009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-90630488295211801939110832707548530000000000000)
      constant := (423196085397886221920437819573967498548923646521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193310737363412106421/100000000000000000000)
  centralHi := (96655368681706053211/50000000000000000000)
  directionLo := (39930094210750450609/20000000000000000000)
  directionHi := (99825235526876126523/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree017.table
  base := (1898989723176747381159692427074833155959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-866193876083741219175148053219792555000000000000)
      constant := (4156761116813207891332033285124190851966645173639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree017.table
  base := (379472627644115323356916735388431637091/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-96268816960015424134983054233892441875000000000)
      constant := (462065800237987381089927096120439352720619891895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39930094210750450609/20000000000000000000)
  centralHi := (99825235526876126523/50000000000000000000)
  directionLo := (205794995089735452903/100000000000000000000)
  directionHi := (25724374386216931613/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree018.table
  base := (621937058068577462507255497317806779789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-50940309485562605633680612298633505000000000000)
      constant := (252515115061711235820265097122459028211158024341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree018.table
  base := (2485035908568149979064619395420688365933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-203814291249638092661710551520472707500000000000)
      constant := (1010529762637184548488733764660172447576695122677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205794995089735452903/100000000000000000000)
  centralHi := (25724374386216931613/12500000000000000000)
  directionLo := (105880651461897551057/50000000000000000000)
  directionHi := (42352260584759020423/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree019.table
  base := (266824541218967676039846861546124875029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-1935314530793025167274707979062027250000000000000)
      constant := (9941239765521739492472797397314407756148153395545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree019.table
  base := (133186740761885387169495321673270702393/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-107545474289622668526727497286580265625000000000)
      constant := (552557913677567564138664516718888557201761672085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105880651461897551057/50000000000000000000)
  centralHi := (42352260584759020423/20000000000000000000)
  directionLo := (27195507104799953793/12500000000000000000)
  directionHi := (43512811367679926069/20000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree020.table
  base := (311040670198522184001765338320966969/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-509194480026449132934228478843312080000000000000)
      constant := (2715571924355491010918345120124332754180029962250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree020.table
  base := (309170140015377814141736805498616116739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-226367605908852581445199437625848355000000000000)
      constant := (1207520913255806545584691554464206555354147968891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27195507104799953793/12500000000000000000)
  centralHi := (43512811367679926069/20000000000000000000)
  directionLo := (223216012508022053521/100000000000000000000)
  directionHi := (111608006254011026761/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree021.table
  base := (-601966245749636225224035212116237572561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-237582367713174210688791094631607710000000000000)
      constant := (1316786601963821642655564695749786735828386477191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree021.table
  base := (-301756997276953302376868142167193802523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-118822131619229912918471940339268089375000000000)
      constant := (658727665090683594721806279320981846746615443613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223216012508022053521/100000000000000000000)
  centralHi := (111608006254011026761/50000000000000000000)
  directionLo := (57182087258588096867/25000000000000000000)
  directionHi := (228728349034352387469/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree022.table
  base := (-710498179114384299419621629361142843371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-1119852349365669630330662893997845230000000000000)
      constant := (6452781666170695899000026703122291412742534992709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree022.table
  base := (-711137115860634786176961203168492059751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-124460460284033535114344161865612001250000000000)
      constant := (717345625918091646073688999874681973443142742081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57182087258588096867/25000000000000000000)
  centralHi := (228728349034352387469/100000000000000000000)
  directionLo := (117055464485836375277/50000000000000000000)
  directionHi := (46822185794334550111/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree023.table
  base := (-107936100254745286120824101550515798493/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-585292022011027656280882931076727882500000000000)
      constant := (3506031114852989160909273488414437788402612860735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree023.table
  base := (-539943733885004857038296548568966319917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-65049394474418578655108191695977956562500000000)
      constant := (389762337171245620649909575006161963080839089027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117055464485836375277/50000000000000000000)
  centralHi := (46822185794334550111/20000000000000000000)
  directionLo := (119686252840477335797/50000000000000000000)
  directionHi := (47874501136190934319/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree024.table
  base := (-2825123921772657307206547394705638671151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-271403497484097998842859740068681400000000000000)
      constant := (1689498982086986497597559074044337811163566415481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree024.table
  base := (-2825989892959898227587737959290604957047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-271474235227281559012177209836599650000000000000)
      constant := (1690388390218986418789009352742536461195976739057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119686252840477335797/50000000000000000000)
  centralHi := (47874501136190934319/20000000000000000000)
  directionLo := (122260445246998987667/50000000000000000000)
  directionHi := (48904178098799595067/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree025.table
  base := (-1714032724978147178947992973398818390313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-1272047433334826677023971798464676835000000000000)
      constant := (8224330177114248344199707458955374638485739613927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree025.table
  base := (-857194108897615831209933950133751079063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-70687723139222200850980413222321868437500000000)
      constant := (457149278823678681641269735608573298005207433353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122260445246998987667/50000000000000000000)
  centralHi := (48904178098799595067/20000000000000000000)
  directionLo := (249563088817190316307/100000000000000000000)
  directionHi := (62390772204297579077/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree026.table
  base := (-993435733835252638725055354449261069227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-661389563995606179627537383310143685000000000000)
      constant := (4438210833507193497169878549029274009511624825733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree026.table
  base := (-3974325746381048130978298032905192463151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-294027549886496047795666095941975297500000000000)
      constant := (1973587855715294926389761883079993639213005567481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249563088817190316307/100000000000000000000)
  centralHi := (62390772204297579077/25000000000000000000)
  directionLo := (127252705975134272587/50000000000000000000)
  directionHi := (10180216478010741807/4000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree027.table
  base := (-1116759923416726001787277508694514403541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-76306156813755446749232096376438772500000000000)
      constant := (531039373361063028764641248364678433547925241571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree027.table
  base := (-893503346734762901426725168332481989759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-305304207216103292187410538994663121250000000000)
      constant := (2125291525314066496484099994892338327419968953645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127252705975134272587/50000000000000000000)
  centralHi := (10180216478010741807/4000000000000000000)
  directionLo := (129676784857559381209/50000000000000000000)
  directionHi := (259353569715118762419/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree028.table
  base := (-982360903624538037425629271618988899929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-2848485034607967447434561405863016880000000000000)
      constant := (20541892179078997489092342075735957810554657239955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree028.table
  base := (-122804861222252809545538366273053645281/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-79145216136427634144788745511837736250000000000)
      constant := (570913419378272357913042853073261314086299875110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129676784857559381209/50000000000000000000)
  centralHi := (259353569715118762419/100000000000000000000)
  directionLo := (33014093471570507299/12500000000000000000)
  directionHi := (264112747772564058393/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree029.table
  base := (-5311070970347296637425507480434297489653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-2949948423920738811896767342174237950000000000000)
      constant := (22025880946561647170539056034630361314852139917787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree029.table
  base := (-265569464630137652712055922362421901579/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-81964380468829445242724856275009692187500000000)
      constant := (612157850332028756773051849946370979713496840745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33014093471570507299/12500000000000000000)
  centralHi := (264112747772564058393/100000000000000000000)
  directionLo := (268787672611623157899/100000000000000000000)
  directionHi := (2687876726116231579/1000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree030.table
  base := (-2833615059996461975311871845653762470821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-169522878512972787575498515471414390000000000000)
      constant := (1309393278994051371963966960603183882927317071251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree030.table
  base := (-1416872418905962449310021536973354552069/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-84783544801231256340660967038181648125000000000)
      constant := (655047719114600582903385321959639278975471160339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268787672611623157899/100000000000000000000)
  centralHi := (2687876726116231579/1000000000000000000)
  directionLo := (273382666531680802487/100000000000000000000)
  directionHi := (34172833316460100311/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree031.table
  base := (-2991083325138467581806428823329341914469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-1576437601273140770410589607398340045000000000000)
      constant := (12585623109088503072249474398124626616241018732651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree031.table
  base := (-5982378053444026066084565281907739601541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-350410836534532269754388311205414416250000000000)
      constant := (2798305447016069139174240770665355187763874279571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273382666531680802487/100000000000000000000)
  centralHi := (34172833316460100311/12500000000000000000)
  directionLo := (55580338887765432431/20000000000000000000)
  directionHi := (69475423609706790539/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree032.table
  base := (-782170764450203401069715826003249927431/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-813584647964763226320846287776975290000000000000)
      constant := (6708048303525333637763240192454361276610107474898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree032.table
  base := (-782192265052376689258980886390850931251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-90421873466034878536533188564525560000000000000)
      constant := (745738525909573485861241699259817231519356917162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55580338887765432431/20000000000000000000)
  centralHi := (69475423609706790539/25000000000000000000)
  directionLo := (141174201949196734743/50000000000000000000)
  directionHi := (282348403898393469487/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree033.table
  base := (-6493999473665920826533319632199377503027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-372866886796869363305065676379902470000000000000)
      constant := (3172418975670636977301377775548516060362339668437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree033.table
  base := (-811767410752760698896800838609298751891/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-93241037798436689634469299327697515937500000000)
      constant := (793530071822326247847724018431034060135890615842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141174201949196734743/50000000000000000000)
  centralHi := (282348403898393469487/100000000000000000000)
  directionLo := (286726159594776781591/100000000000000000000)
  directionHi := (35840769949347097699/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree034.table
  base := (-3346494855460458790958257169841007742659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-1728632685242297817103898511865171650000000000000)
      constant := (15164930646091505051493798862709531640102760455661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree034.table
  base := (-6693103251630114144377027192184664976337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-384240808523354002929621640363477887500000000000)
      constant := (3371790946521838244967381932204016536445437079047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286726159594776781591/100000000000000000000)
  centralHi := (35840769949347097699/12500000000000000000)
  directionLo := (18189879570275523639/6250000000000000000)
  directionHi := (11641522924976335129/4000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree035.table
  base := (-1713766089100337281210421536224843862107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-889682189949341749667500740010391092500000000000)
      constant := (8041593007534102152389647337266328772100569655253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree035.table
  base := (-685515648232475388154755843848005937333/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-197758732926480623660683041708082855625000000000)
      constant := (1787977897233782437355684994132387791255400303615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18189879570275523639/6250000000000000000)
  centralHi := (11641522924976335129/4000000000000000000)
  directionLo := (295287028871854700089/100000000000000000000)
  directionHi := (29528702887185470009/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree036.table
  base := (-6980796873715053135475323607348207304803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-406688016567793151459134321816976160000000000000)
      constant := (3784581101313500814882649557291559462716955008293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree036.table
  base := (-6980871562856399982609363400410312361521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-406794123182568491713110526468853535000000000000)
      constant := (3786606723229652462058360015448554074493073542951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295287028871854700089/100000000000000000000)
  centralHi := (29528702887185470009/10000000000000000000)
  directionLo := (18717231661289273723/6250000000000000000)
  directionHi := (299475706580628379569/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree037.table
  base := (-7070639287083973463152047980276772955493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-3761655538422909727594414832664006510000000000000)
      constant := (36014377330583932910407568754622338821080306775147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree037.table
  base := (-707069979300355068166768710743268603023/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-209035390256087868052427484760770679375000000000)
      constant := (2001868671163483904723610090175913601465095795565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18717231661289273723/6250000000000000000)
  centralHi := (299475706580628379569/100000000000000000000)
  directionLo := (303606601120538380529/100000000000000000000)
  directionHi := (30360660112053838053/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree038.table
  base := (-222654621814849772110357628635011955369/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-965779731933920273014155192243806895000000000000)
      constant := (9506442219702510412229126497552955317936724190008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree038.table
  base := (-1781249219579283864420984973911930408989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-107336859460445745124149853143557295625000000000)
      constant := (1056835653727198879337193742034266125659664140859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303606601120538380529/100000000000000000000)
  centralHi := (30360660112053838053/10000000000000000000)
  directionLo := (307682039865775672011/100000000000000000000)
  directionHi := (76920509966443918003/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree039.table
  base := (-7144003556319490353810970929026632850829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-440509146338716939613202967254049850000000000000)
      constant := (4455040973843968302606832952568329920831309569899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree039.table
  base := (-285761727157367932308814644487295465717/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-440624095171390224888343855626917006250000000000)
      constant := (4457418571028214179604187495329653449867526845675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307682039865775672011/100000000000000000000)
  centralHi := (76920509966443918003/25000000000000000000)
  directionLo := (31170419802749504003/10000000000000000000)
  directionHi := (311704198027495040031/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree040.table
  base := (-7128027637559612695594860349804724502153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-4066045706361223820981032641597669720000000000000)
      constant := (42223148775479584041668504613956226656459653905287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree040.table
  base := (-7128059669239454764725838081005336314323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-451900752500997469280088298679604830000000000000)
      constant := (4693962081650591553249976661462775135387349199413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31170419802749504003/10000000000000000000)
  centralHi := (311704198027495040031/100000000000000000000)
  directionLo := (63135022445537442193/20000000000000000000)
  directionHi := (157837556113843605483/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree041.table
  base := (-3538597319047706307108819474606770270937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-2083754547836997592721619288954445395000000000000)
      constant := (22204543336693893740132012768384327753524206624823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree041.table
  base := (-7077220516934043827892138840957057997653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-463177409830604713671832741732292653750000000000)
      constant := (4936970680531845168565095955295114694315119416643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63135022445537442193/20000000000000000000)
  centralHi := (157837556113843605483/50000000000000000000)
  directionLo := (63919338510958321271/20000000000000000000)
  directionHi := (79899173138697901589/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree042.table
  base := (-873955262770878842965092562255345904443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-118582569027410181941817903172780885000000000000)
      constant := (1295921248040921020210886517910612579179258538266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree042.table
  base := (-1747915749400548056762263441787299911913/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-118613516790052989515894296196245119375000000000)
      constant := (1296610605956625700330209568670340699435814306703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63919338510958321271/20000000000000000000)
  centralHi := (79899173138697901589/25000000000000000000)
  directionLo := (32347073330358816479/10000000000000000000)
  directionHi := (323470733303588164791/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree043.table
  base := (-6871478447071051436803412326768874418881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-4370435874299537914367650450531332930000000000000)
      constant := (48955369726870512365639379402645307716099814241999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree043.table
  base := (-687149530917608510929929679183663171809/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-242865362244909601227660813918834150625000000000)
      constant := (2721187889716779629647469664991067964486636371395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32347073330358816479/10000000000000000000)
  centralHi := (323470733303588164791/100000000000000000000)
  directionLo := (327298922570729117843/100000000000000000000)
  directionHi := (81824730642682279461/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree044.table
  base := (-1343357826239460764326507935850540476201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-4471899263612309278829856386842554000000000000000)
      constant := (51315690174632672359382728013048338705204401291395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree044.table
  base := (-3358401365572165903473762122030479805889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-248503690909713223423533035445178062500000000000)
      constant := (2852384769890521800383494014045642673735024564759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327298922570729117843/100000000000000000000)
  centralHi := (81824730642682279461/25000000000000000000)
  directionLo := (331082850851503946129/100000000000000000000)
  directionHi := (33108285085150394613/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree045.table
  base := (-3263820757948696945405088492081332537293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-254075702940282257960670129064098615000000000000)
      constant := (2985228760451473968074002217326492063276732317483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree045.table
  base := (-130553049582414052461788677585085408541/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-254142019574516845619405256971521974375000000000)
      constant := (2986811376542252699758984032809486015949228664275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331082850851503946129/100000000000000000000)
  centralHi := (33108285085150394613/10000000000000000000)
  directionLo := (167412009381016540141/50000000000000000000)
  directionHi := (334824018762033080283/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree046.table
  base := (-6304088697784874667726588395567052364487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-4674826042237852007754268259464996140000000000000)
      constant := (56210645500638898416972311258744621819183130335273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree046.table
  base := (-394006095695098499747953572421166224919/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-129890174119660233907638739248932943125000000000)
      constant := (1562233667291569863023603345533939536866907294756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167412009381016540141/50000000000000000000)
  centralHi := (334824018762033080283/100000000000000000000)
  directionLo := (84630960998309209591/25000000000000000000)
  directionHi := (67704768798647367673/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree047.table
  base := (-6046172529492690508663109343464902249413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-4776289431550623372216474195776217210000000000000)
      constant := (58745268278406573050830682762541366314718485922827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree047.table
  base := (-6046179643364220601400460663638186996121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-530837353808248180022299400048419596250000000000)
      constant := (6530704696751272433328314117363074796461011795551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84630960998309209591/25000000000000000000)
  centralHi := (67704768798647367673/20000000000000000000)
  directionLo := (342183667587973032327/100000000000000000000)
  directionHi := (42772958448496629041/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree048.table
  base := (-115078520014868028208205610299765776231/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-270986267825744152037704451782635460000000000000)
      constant := (3407665656509396384050134044427032998703821424025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree048.table
  base := (-5753931727261063890868549055114009302959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-542114011137855424414043843101107420000000000000)
      constant := (6818932369808322341806481185262592264002528359929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342183667587973032327/100000000000000000000)
  centralHi := (42772958448496629041/12500000000000000000)
  directionLo := (34580475962015834989/10000000000000000000)
  directionHi := (345804759620158349891/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree049.table
  base := (-2713687557597416429029911665094874320629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-2489608105088083050570443034199329675000000000000)
      constant := (31994391401490439579907424783950264821025198563291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree049.table
  base := (-5427379722920927158837955720209490178751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-553390668467462668805788286153795243750000000000)
      constant := (7113617321021104389608471124246534110344733131081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34580475962015834989/10000000000000000000)
  centralHi := (345804759620158349891/100000000000000000000)
  directionLo := (34938832434406644283/10000000000000000000)
  directionHi := (349388324344066442831/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree050.table
  base := (-1013308073967535284607151687957717634921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-5080679599488937465603092004709880420000000000000)
      constant := (66697668623674136134863835739520095154585725225795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree050.table
  base := (-253327203790335665648199678641002900483/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-141166831449267478299383182301620766875000000000)
      constant := (1853689815219602147082823327426564655303040191865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34938832434406644283/10000000000000000000)
  centralHi := (349388324344066442831/100000000000000000000)
  directionLo := (176467752436495918429/50000000000000000000)
  directionHi := (352935504872991836859/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree051.table
  base := (-583929740138768777454608272422450810619/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-143948416355603023057369387250586152500000000000)
      constant := (1929573256117995704973149525003672191129895930778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree051.table
  base := (-583930112576076925318822804469943622147/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-143985995781669289397319293064792722812500000000)
      constant := (1930589490298374605438544726147067955184149549314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176467752436495918429/50000000000000000000)
  centralHi := (352935504872991836859/100000000000000000000)
  directionLo := (71289477487761885689/20000000000000000000)
  directionHi := (178223693719404714223/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree052.table
  base := (-2121040252035850663763903384162763222577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-2641803189057240097263751938666161280000000000000)
      constant := (36144843484863330465536009290716530883351925580383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree052.table
  base := (-4242082898586588899835434233793176718347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-587220640456284401981021615311858715000000000000)
      constant := (8036413242114386407457767099864582998496341079357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71289477487761885689/20000000000000000000)
  centralHi := (178223693719404714223/50000000000000000000)
  directionLo := (359925005277421355219/100000000000000000000)
  directionHi := (17996250263871067761/5000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree053.table
  base := (-59038721202014098215527538738070145387/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 113422500000000000000000000000000000000000000
      center := (1542546)
      previous := (771273)
      next := (771273)
      square := (8528569414017914753559090886747500000000000)
      linear := (-479269292223856493324110876970767500000000000)
      constant := (6690353915345876564115512211288626804182995152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree053.table
  base := (-3778480080602018571147419218441991752921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (685576)
      previous := (342788)
      next := (342788)
      square := (3790475295119073223804040394110000000000000)
      linear := (-213064185755034405971080832454448750000000000)
      constant := (2975053386217722855669923667922599349261025239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359925005277421355219/100000000000000000000)
  centralHi := (17996250263871067761/5000000000000000000)
  directionLo := (363369342179483908229/100000000000000000000)
  directionHi := (36336934217948390823/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree054.table
  base := (-656127758426579739178823586907898299733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-609614795193335880383546194439418300000000000000)
      constant := (8679336120130206775042285441993770973204840325615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree054.table
  base := (-3280640336997330251314171861995057024907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-609773955115498890764510501417234362500000000000)
      constant := (8683893008778507486420198964580428593331429670717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363369342179483908229/100000000000000000000)
  centralHi := (36336934217948390823/10000000000000000000)
  directionLo := (183390667870498481501/50000000000000000000)
  directionHi := (366781335740996963003/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree055.table
  base := (-274856864653899903347610976812683168487/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-2793998273026397143957060843132992885000000000000)
      constant := (40556655819964554932473682300538845518334587256365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree055.table
  base := (-687142471691021878237546505890318403131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-155262653111276533789063736117480546562500000000)
      constant := (2254329323682796703056363059781919958399026785861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183390667870498481501/50000000000000000000)
  centralHi := (366781335740996963003/100000000000000000000)
  directionLo := (370161880344193476871/100000000000000000000)
  directionHi := (46270235043024184609/12500000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree056.table
  base := (-2182272636238668261356663041447265010621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-5689459935365565652376327622577206840000000000000)
      constant := (84170675642583842073122684701066219785756378605459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree056.table
  base := (-2182273631568586699491624627692977982251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-632327269774713379547999387522610010000000000000)
      constant := (9357197750335198341165437299113139959158046839581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370161880344193476871/100000000000000000000)
  centralHi := (46270235043024184609/12500000000000000000)
  directionLo := (373511829895584541411/100000000000000000000)
  directionHi := (93377957473896135353/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree057.table
  base := (-395438659062715428384880755297109539647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-160858981241064917134403709969122997500000000000)
      constant := (2424614349869381889675278582261841685582086279657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree057.table
  base := (-158175543478795793046039284863829485047/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-321801963552160311969871915287648916875000000000)
      constant := (4851767160442234500006366884033740538050101285285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373511829895584541411/100000000000000000000)
  centralHi := (93377957473896135353/25000000000000000000)
  directionLo := (94208000086227800037/25000000000000000000)
  directionHi := (376832000344911200149/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree058.table
  base := (-118377212623096774952637678882790977237/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-1473096678497777095325184873799912245000000000000)
      constant := (22614908527203068546897281318986461911771680685046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree058.table
  base := (-947018341440987323531701349588694728577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-654880584433927868331488273627985657500000000000)
      constant := (10056326963261018169166206775889309882622690550487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94208000086227800037/25000000000000000000)
  centralHi := (376832000344911200149/100000000000000000000)
  directionLo := (95030793001514194641/25000000000000000000)
  directionHi := (76024634401211355713/20000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree059.table
  base := (-278064238016478390645474354894341426593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-5993850103303879745762945431510870050000000000000)
      constant := (93691227876302263926555583930462427261801678232047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree059.table
  base := (-278064751533295054665647336651068662653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-666157241763535112723232716680673481250000000000)
      constant := (10415575643480360665984451608883724969448417031643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95030793001514194641/25000000000000000000)
  centralHi := (76024634401211355713/20000000000000000000)
  directionLo := (191693045849311719791/50000000000000000000)
  directionHi := (383386091698623439583/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree060.table
  base := (425103854934115082863139607600326628553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-677257054735183456691683485313565680000000000000)
      constant := (10775655295102156155830147719921316109515510705457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree060.table
  base := (425103443315394322337608863636570458769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-677433899093142357114977159733361305000000000000)
      constant := (10781280334756841507052208404599852889151576571961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191693045849311719791/50000000000000000000)
  centralHi := (383386091698623439583/100000000000000000000)
  directionLo := (386621474726824212843/100000000000000000000)
  directionHi := (96655368681706053211/25000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree061.table
  base := (116248508203313172858644897180307122943/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-3098388440964711237343678652066656095000000000000)
      constant := (50164321628516177243356108019756478838724949581515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree061.table
  base := (1162484752184328393050276121579103608011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-688710556422749601506721602786049128750000000000)
      constant := (11153441015978770872574021602344509837825133013859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386621474726824212843/100000000000000000000)
  centralHi := (96655368681706053211/25000000000000000000)
  directionLo := (12182187709704526709/3125000000000000000)
  directionHi := (389830006710544854689/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree062.table
  base := (1934078264226839641401496795605650051453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-6298240271242193839149563240444533260000000000000)
      constant := (103734464529380710244563146286405981988750898580013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree062.table
  base := (1934077999975025750973590916351409663939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-699987213752356845898466045838736952500000000000)
      constant := (11532057670506555674190511012371777080948359445691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12182187709704526709/3125000000000000000)
  centralHi := (389830006710544854689/100000000000000000000)
  directionLo := (393012345281853098343/100000000000000000000)
  directionHi := (49126543160231637293/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree063.table
  base := (2739882472158167232192075477339740097739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-711078184506107244845752130750639370000000000000)
      constant := (11910929039391754880066807075273616077700060757891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree063.table
  base := (1369941130256575320113311697205379467179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-355631935540982045145105244445712388125000000000)
      constant := (5958565142612705397067829962039172158679228343251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393012345281853098343/100000000000000000000)
  centralHi := (49126543160231637293/12500000000000000000)
  directionLo := (99042280414711521897/25000000000000000000)
  directionHi := (396169121658846087589/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree064.table
  base := (3579896973289133724306041508600470679179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-6501167049867736568073975113066975400000000000000)
      constant := (110720333639111851054381257756061252804670474791259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree064.table
  base := (178994840191037613214818251938177860557/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-180635132102892833670488732986028150000000000000)
      constant := (3077164712449681270714289881541285720287727770665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99042280414711521897/25000000000000000000)
  centralHi := (396169121658846087589/100000000000000000000)
  directionLo := (399300942107504506091/100000000000000000000)
  directionHi := (99825235526876126523/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree065.table
  base := (1113530297555222576809171056245460096481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-1650657609795126983134045262344549117500000000000)
      constant := (28575095327388573532460778133605821230915345387601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree065.table
  base := (4454121054557309920331397776157267267639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-733817185741178579073699374996800423750000000000)
      constant := (12706643356079579534654634956825262465517623970991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399300942107504506091/100000000000000000000)
  centralHi := (99825235526876126523/25000000000000000000)
  directionLo := (402408389301142351329/100000000000000000000)
  directionHi := (40240838930114235133/10000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree066.table
  base := (5362554667840119524963279809545418469647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-744899314277031032999820776187713060000000000000)
      constant := (13104278256428087749226188484644120208705922890343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree066.table
  base := (670319319907976625547311326834431553061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-186273460767696455866360954512372061875000000000)
      constant := (3277770949411729481200829099279282173300239954618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402408389301142351329/100000000000000000000)
  centralHi := (40240838930114235133/10000000000000000000)
  directionLo := (81098404717217171879/20000000000000000000)
  directionHi := (101373005896521464849/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree067.table
  base := (6305197047422686116565492300495634230123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-6805557217806050661460592922000638610000000000000)
      constant := (121634702588290988476897589763380418247646539137083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree067.table
  base := (6305196960545220775426529557181368610279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-756370500400393067857188261102176071250000000000)
      constant := (13521980169439966076648601241963019752040033277151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81098404717217171879/20000000000000000000)
  centralHi := (101373005896521464849/25000000000000000000)
  directionLo := (25534524010085489717/6250000000000000000)
  directionHi := (408552384161367835473/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree068.table
  base := (1820512011555310476010371948331366901539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-1726755151779705506480699714577964920000000000000)
      constant := (31347244028708784555226915071398387659941187400819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree068.table
  base := (3641023988360808337911422326322496178607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-383823578865000156124466352077431947500000000000)
      constant := (6969666233735044383914114720777564392828429304583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25534524010085489717/6250000000000000000)
  centralHi := (408552384161367835473/100000000000000000000)
  directionLo := (205794995089735452903/50000000000000000000)
  directionHi := (411589990179470905807/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree069.table
  base := (8293107441375478601394050099521361441113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-778720444047954821153889421624786750000000000000)
      constant := (14355702762120398035174391077289609844616243628097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree069.table
  base := (8293107385789679718877357279037002419287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-778923815059607556640677147207551718750000000000)
      constant := (14363140688593681454609422731982233482252700279503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205794995089735452903/50000000000000000000)
  centralHi := (411589990179470905807/100000000000000000000)
  directionLo := (207302670887241603321/50000000000000000000)
  directionHi := (414605341774483206643/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree070.table
  base := (14591211026921320678895038239377505151/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-1777486846436091188711802682733575455000000000000)
      constant := (33267937199662621171835690983083624553440603947360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree070.table
  base := (9338375012781462223286610096571150665147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-790200472389214801032421590260239542500000000000)
      constant := (14793404830333168428241766017028670144411693929843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207302670887241603321/50000000000000000000)
  centralHi := (414605341774483206643/100000000000000000000)
  directionLo := (417598921023432605407/100000000000000000000)
  directionHi := (13049966281982268919/3125000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree071.table
  base := (2083570151067158423773746191061597687889/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252810000000000000000000000000000000000000000
      center := (3438216)
      previous := (1719108)
      next := (1719108)
      square := (19009523097779268036300326364510000000000000)
      linear := (-1430551631632044459295658930221290000000000000)
      constant := (27177196571293756803433283746940008755737609045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree071.table
  base := (10417850719800856551076852972665876458129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (382024)
      previous := (191012)
      next := (191012)
      square := (2112169233086585337366702929390000000000000)
      linear := (-158991694052533633291840117697466250000000000)
      constant := (3021250722224939000224034948869928876658384361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417598921023432605407/100000000000000000000)
  centralHi := (13049966281982268919/3125000000000000000)
  directionLo := (42057119284603192537/10000000000000000000)
  directionHi := (420571192846031925371/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree072.table
  base := (11531534426573999182029967125751117782329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-812541573818878609307958067061860440000000000000)
      constant := (15665202466322355978602888049236563599736683853601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree072.table
  base := (72072089988566015309501673373613162109/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-203188446762107322453977619091403797500000000000)
      constant := (3918325217065759933057459149100619302518513456840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42057119284603192537/10000000000000000000)
  centralHi := (420571192846031925371/100000000000000000000)
  directionLo := (423522605847590204229/100000000000000000000)
  directionHi := (42352260584759020423/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree073.table
  base := (2535885196988257123549209942853696294043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-7414337553682678848233828539867965030000000000000)
      constant := (145031471630718261286819372092220654668424515797015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree073.table
  base := (6339712981121254079394082215782763625163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-412015222189018267103827459709151506875000000000)
      constant := (8061466380850871976949946806752077962621704482547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423522605847590204229/100000000000000000000)
  centralHi := (42352260584759020423/10000000000000000000)
  directionLo := (426453593109417148391/100000000000000000000)
  directionHi := (53306699138677143549/12500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree074.table
  base := (2772305072531166477240349817811200458379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-7515800942995450212696034476179186100000000000000)
      constant := (149134196208704782369706509892357949376258584772295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree074.table
  base := (138615253445193717117618542616456614093/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-208826775426910944649849840617747709375000000000)
      constant := (4144755142524064169759429538071191702910304042925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426453593109417148391/100000000000000000000)
  centralHi := (53306699138677143549/12500000000000000000)
  directionLo := (429364572930663894147/100000000000000000000)
  directionHi := (107341143232665973537/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree075.table
  base := (7538916253148989946300559155079656219227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-423181351794901198731013356249467065000000000000)
      constant := (8516388662447382465890242593382104234276155369363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree075.table
  base := (7538916245904742128602227938416994640289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-423291879518625511495571902761839330625000000000)
      constant := (8520782146346687443658880056875134195074680198841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429364572930663894147/100000000000000000000)
  centralHi := (107341143232665973537/25000000000000000000)
  directionLo := (432255949525197937363/100000000000000000000)
  directionHi := (108063987381299484341/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree076.table
  base := (8164173686884223762704127820924163699517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-3859363860810496470810223174400814120000000000000)
      constant := (78756935385698685490816498497236226587519433445357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree076.table
  base := (8164173681098111710834264051679519550959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-428930208183429133691444124288183242500000000000)
      constant := (8755281964449776061011411309131249126617883552071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432255949525197937363/100000000000000000000)
  centralHi := (108063987381299484341/25000000000000000000)
  directionLo := (27195507104799953793/6250000000000000000)
  directionHi := (435128113676799260689/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree077.table
  base := (8806534965945357661510230954055256602557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-3910095555466882153041326142556424655000000000000)
      constant := (80895410373255087995569445626222598103225156569197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree077.table
  base := (17613069922649370385325032063825983141669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-869137073696465511774632691629054308750000000000)
      constant := (17986019478247074902557145924209975360494371482061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27195507104799953793/6250000000000000000)
  centralHi := (435128113676799260689/100000000000000000000)
  directionLo := (437981443355684434317/100000000000000000000)
  directionHi := (218990721677842217159/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree078.table
  base := (2366500019315144494472978494479725124907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-220045958340181546404023839484001955000000000000)
      constant := (4614606829057208771755382968575783087184458458566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree078.table
  base := (18932000147142448860692058932347763041683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-880413731026072756166377134681742132500000000000)
      constant := (18467930940367403926215493618175547390660935324427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437981443355684434317/100000000000000000000)
  centralHi := (218990721677842217159/50000000000000000000)
  directionLo := (220408152149556213737/50000000000000000000)
  directionHi := (17632652171964497099/4000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree079.table
  base := (20285138021059392415837826462131078766829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-8023117889559307035007064157735291450000000000000)
      constant := (170518946067420046978742509285429117006915492106909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree079.table
  base := (20285138015168867838528195835651821567839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-891690388355680000558121577734429956250000000000)
      constant := (18956298314970162398693126732074899350238132704791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220408152149556213737/50000000000000000000)
  centralHi := (17632652171964497099/4000000000000000000)
  directionLo := (354906440446877669/80000000000000000)
  directionHi := (443633050558597086251/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree080.table
  base := (21672483515274126738907241136770521027887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-8124581278872078399469270094046512520000000000000)
      constant := (174970121408523228277413621275918381827756402696127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree080.table
  base := (5418120877643098115123209328691419012843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-225741761421321811237466505196779445000000000000)
      constant := (4862780400456643825998062808261664579571670050467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354906440446877669/80000000000000000)
  centralHi := (443633050558597086251/100000000000000000000)
  directionLo := (446432025016044107043/100000000000000000000)
  directionHi := (111608006254011026761/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree081.table
  base := (23094036624377633157655260632095692890529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-914004963131649973770164003373081510000000000000)
      constant := (19942152429748819161920758609195564443001989139401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree081.table
  base := (4618807324125072208206741091731675483197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-914243703014894489341610463839805603750000000000)
      constant := (19952400800756416801670622007535659091655818401465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446432025016044107043/100000000000000000000)
  centralHi := (111608006254011026761/25000000000000000000)
  directionLo := (449213559870942569353/100000000000000000000)
  directionHi := (224606779935471284677/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree082.table
  base := (1534362333643516025048702803198206505071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-2081877014374405282098420491667238665000000000000)
      constant := (46011674360946169392139412950171297663413369811964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree082.table
  base := (4909959467060433938969364377989321598339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-925520360344501733733354906892493427500000000000)
      constant := (20460135911617722646385278105345808114357901796455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449213559870942569353/100000000000000000000)
  centralHi := (224606779935471284677/50000000000000000000)
  directionLo := (451977977100570661397/100000000000000000000)
  directionHi := (225988988550285330699/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree083.table
  base := (1301988282454770363493088030031987910339/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-2107242861702598123213971975745043932500000000000)
      constant := (47168024533911986873817401437654083661611068928095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree083.table
  base := (3254970705838332759364209964623764263907/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-234199254418527244531274837486295312812500000000)
      constant := (5243581733574670482453003705690953676815464315566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451977977100570661397/100000000000000000000)
  centralHi := (225988988550285330699/50000000000000000000)
  directionLo := (227362794447510172481/50000000000000000000)
  directionHi := (454725588895020344963/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree084.table
  base := (27563941550526337570150947067047228439131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-947826092902573761924232648810155200000000000000)
      constant := (21483952660281425807015278663656295445679701173139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree084.table
  base := (13781970774310411587792876765660492570219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-474036837501858111258421896498934537500000000000)
      constant := (10747486934355623254313156542702489612355045407011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227362794447510172481/50000000000000000000)
  centralHi := (454725588895020344963/100000000000000000000)
  directionLo := (57182087258588096867/12500000000000000000)
  directionHi := (457456698068704774937/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree085.table
  base := (14561162518834452508566667702125796110817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-4315949112717967610890149887801308935000000000000)
      constant := (99048562431906150727943273626408848333448403032657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree085.table
  base := (5824465007229816351050123552915994727953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-959350332333323466908588236050556898750000000000)
      constant := (22022076714786094266695401114721413670246805020285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57182087258588096867/12500000000000000000)
  centralHi := (457456698068704774937/100000000000000000000)
  directionLo := (460171598449883905757/100000000000000000000)
  directionHi := (230085799224941952879/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree086.table
  base := (7678729026662500016329655850729609262439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-2183340403687176646560626427978459735000000000000)
      constant := (50724187724748190025509955196510552421640914329719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree086.table
  base := (7678729026359492197192992829845868635827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-242656747415732677825083169775811180625000000000)
      constant := (5638908868117164857846770909784820184577297274763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460171598449883905757/100000000000000000000)
  centralHi := (230085799224941952879/50000000000000000000)
  directionLo := (462870575249626630171/100000000000000000000)
  directionHi := (115717643812406657543/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree087.table
  base := (32341714754421611413893060994396976868027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-981647222673497550078301294247228890000000000000)
      constant := (23083828005298418333932937302901943053040353016563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree087.table
  base := (32341714753455169308936522108094453433517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-981903646992537955692077122155932546250000000000)
      constant := (23095650141716003910304390983651277210885918484373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462870575249626630171/100000000000000000000)
  centralHi := (115717643812406657543/25000000000000000000)
  directionLo := (116388476352880222987/25000000000000000000)
  directionHi := (465553905411520891949/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree088.table
  base := (34002720978585900144562410104732151935003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-8936288393374249315166917584536281080000000000000)
      constant := (212670228309585731927095979647362586740199875459563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree088.table
  base := (34002720977815386246736143524711660664997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-993180304322145200083821565208620370000000000000)
      constant := (23642120722494351493834963413143028978787009904493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116388476352880222987/25000000000000000000)
  centralHi := (465553905411520891949/100000000000000000000)
  directionLo := (117055464485836375277/25000000000000000000)
  directionHi := (468221857943345501109/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree089.table
  base := (4462241847157165885737757401043410993227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-2259437945671755169907280880211875537500000000000)
      constant := (54411019921113091221806755080030971424884939156534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree089.table
  base := (7139586955328619982526158183945540580909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1004456961651752444475566008261308193750000000000)
      constant := (24195047214777144506212086363109965585664835568105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117055464485836375277/25000000000000000000)
  centralHi := (468221857943345501109/100000000000000000000)
  directionLo := (470874694231827972657/100000000000000000000)
  directionHi := (235437347115913986329/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree090.table
  base := (1169604879654812070049947478522848891571/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-253867088111105334558092484921075645000000000000)
      constant := (6185444615891577986990008911835411022828864283992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree090.table
  base := (1497094245938576291364876788750707501489/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1015733618981359688867310451313996017500000000000)
      constant := (24754429618543512231547569640124905482735049791025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470874694231827972657/100000000000000000000)
  centralHi := (235437347115913986329/50000000000000000000)
  directionLo := (7398635442836419007/1562500000000000000)
  directionHi := (473512668341530816449/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree091.table
  base := (19595492546255979454806190944896714980883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-4620339280656281704276767696734972145000000000000)
      constant := (113883003886185364145313854802683857228817215443043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree091.table
  base := (39190985092121780853227175716729404210951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1027010276310966933259054894366683841250000000000)
      constant := (25320267933777063884706234259625740709138565310719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7398635442836419007/1562500000000000000)
  centralHi := (473512668341530816449/100000000000000000000)
  directionLo := (476136027298833618949/100000000000000000000)
  directionHi := (9522720545976672379/2000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree092.table
  base := (40988821607017812998526416257216760642983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-9342141950625334773015741329781165360000000000000)
      constant := (232914084485157717989128687269327651083034691497143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree092.table
  base := (40988821606706891686855685734501472242481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1038286933640574177650799337419371665000000000000)
      constant := (25892562160464937374487923765038686844577339939289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476136027298833618949/100000000000000000000)
  centralHi := (9522720545976672379/2000000000000000000)
  directionLo := (119686252840477335797/25000000000000000000)
  directionHi := (478745011361909343189/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree093.table
  base := (42820865691755404538326801130215887511361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1049289482215345126386438585121376270000000000000)
      constant := (26457804034485167794483304392300399761145861180009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree093.table
  base := (10705216422876917461639613102857075516863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-262390897742545355510635945118014872187500000000)
      constant := (6617828074649262417556095188964076697506339304847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119686252840477335797/25000000000000000000)
  centralHi := (478745011361909343189/100000000000000000000)
  directionLo := (15041870446172811317/3125000000000000000)
  directionHi := (96267970855505992429/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree094.table
  base := (5585889668270494028337783921923295290461/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-2386267182312719375485038300600901875000000000000)
      constant := (60846115811981409488043989486365055991796973262362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree094.table
  base := (22343558672983292975008829910007698750307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-530420124149894333217144111762373656250000000000)
      constant := (13528259174082753030819759673417193366464810921883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15041870446172811317/3125000000000000000)
  centralHi := (96267970855505992429/20000000000000000000)
  directionLo := (241960391762739161283/50000000000000000000)
  directionHi := (483920783525478322567/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree095.table
  base := (11646894142451249337597695069927094796001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-2411633029640912216600589784678707142500000000000)
      constant := (62176691324444805887323381102229308716788552157521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree095.table
  base := (11646894142411944145400957768965757972979/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-268029226407348977706508166644358784062500000000)
      constant := (6912045077291033662276777225977058270092901948451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241960391762739161283/50000000000000000000)
  centralHi := (483920783525478322567/100000000000000000000)
  directionLo := (486488020551289551257/100000000000000000000)
  directionHi := (243244010275644775629/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree096.table
  base := (24261121681168183535467930440131854458493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-541555305993134457270253615279224980000000000000)
      constant := (14115952358882425550818036637724115601415664365317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree096.table
  base := (1940889734488445593810530733834584433607/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1083393562959003155217777109630122960000000000000)
      constant := (28246298181588119532301808632686122660616109989575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486488020551289551257/100000000000000000000)
  centralHi := (243244010275644775629/50000000000000000000)
  directionLo := (489041780987995950669/100000000000000000000)
  directionHi := (48904178098799595067/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree097.table
  base := (50491117723491657633441033562456516159909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-9849458897189191595326771011337270710000000000000)
      constant := (259525594734204996148745244596181174783279882181589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree097.table
  base := (50491117723391924267508640918661150007537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1094670220288610399609521552682810783750000000000)
      constant := (28850871965433711785616038910936322035770762693753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489041780987995950669/100000000000000000000)
  centralHi := (48904178098799595067/10000000000000000000)
  directionLo := (491582274867503812609/100000000000000000000)
  directionHi := (49158227486750381261/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree098.table
  base := (6561774956633008527690439689447634868127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-2487730571625490739947244236912122945000000000000)
      constant := (66255530530179219310192854113908141612393478602334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree098.table
  base := (26247099826492323548307159546577000384799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-552973438809108822000632997867749303750000000000)
      constant := (14730950830349000869279389890229927427821193871031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491582274867503812609/100000000000000000000)
  centralHi := (49158227486750381261/10000000000000000000)
  directionLo := (494109706822188571601/100000000000000000000)
  directionHi := (247054853411094285801/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree099.table
  base := (10906297830178732763136202034245655900293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1116931741757192702694575875995523650000000000000)
      constant := (30064080513266546758739626328340887922819980147585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree099.table
  base := (27265744575415212307692271050476494376327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-558611767473912444196505219394093215625000000000)
      constant := (15039693633689369785421595531346373196579933669263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494109706822188571601/100000000000000000000)
  centralHi := (247054853411094285801/50000000000000000000)
  directionLo := (496624276277255919193/100000000000000000000)
  directionHi := (248312138138627959597/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree100.table
  base := (56602986216857340604627878830407520947383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-10153849065127505688713388820270933920000000000000)
      constant := (276189402230235438375449768097880752519373850489543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree100.table
  base := (56602986216806991425858143437341684120183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1128500192277432132784754881840874255000000000000)
      constant := (30703328785474193983771290384491072704761407590927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496624276277255919193/100000000000000000000)
  centralHi := (248312138138627959597/50000000000000000000)
  directionLo := (249563088817190316307/50000000000000000000)
  directionHi := (99825235526876126523/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree101.table
  base := (58708690850860921355220726864707313568701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-10255312454440277053175594756582154990000000000000)
      constant := (281860154953214427791315443806639818028519193434221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree101.table
  base := (3669293178176302427409649733647059872689/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-284944212401759844294124831223390519687500000000)
      constant := (7833431553745760219624265531034533683662125772764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249563088817190316307/50000000000000000000)
  centralHi := (99825235526876126523/20000000000000000000)
  directionLo := (501615600447101686963/100000000000000000000)
  directionHi := (125403900111775421741/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree102.table
  base := (60848603052832929420036481509810112430329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1150752871528116490848644521432597340000000000000)
      constant := (31954331420925197775954454106418542819922459365601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree102.table
  base := (60848603052801023226389261110021689659401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1151053506936646621568243767946249902500000000000)
      constant := (31970579555904275681271523327852982294711420598769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501615600447101686963/100000000000000000000)
  centralHi := (125403900111775421741/25000000000000000000)
  directionLo := (504092729588421494253/100000000000000000000)
  directionHi := (252046364794210747127/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree103.table
  base := (63022722822719685652427936184678528730263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-10458239233065819782100006629204597130000000000000)
      constant := (293375885735565654000178995494173339984926915450023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree103.table
  base := (31511361411347145178577905541308759489749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-581165082133126932979994105499468863125000000000)
      constant := (16306944404118572151583329322766661049832543357581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504092729588421494253/100000000000000000000)
  centralHi := (252046364794210747127/50000000000000000000)
  directionLo := (506557745411028640723/100000000000000000000)
  directionHi := (126639436352757160181/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree104.table
  base := (65231050160481447845733343444956842420273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-10559702622378591146562212565515818200000000000000)
      constant := (299220863794925985033817299989032626017396912355233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree104.table
  base := (3261552508023061835779422971854893960881/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-293401705398965277587933163512906387500000000000)
      constant := (8315913492995272195936778324108360096690771744445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506557745411028640723/100000000000000000000)
  centralHi := (126639436352757160181/25000000000000000000)
  directionLo := (127252705975134272587/25000000000000000000)
  directionHi := (509010823900537090349/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree105.table
  base := (67473585066089371703285102768976008550437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1184574001299040279002713166869671030000000000000)
      constant := (33902657440711566347051722911160316325519632943853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree105.table
  base := (2698943402642931517447195865797887659451/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1184883478925468354743477097104313373750000000000)
      constant := (33919875047135704505168236006894246239825702680475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127252705975134272587/25000000000000000000)
  centralHi := (509010823900537090349/100000000000000000000)
  directionLo := (20458085472884412747/4000000000000000000)
  directionHi := (127863034205527579669/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree106.table
  base := (13950065507904623831625798838933802801989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6170184)
      previous := (3085092)
      next := (3085092)
      square := (34114277656071659014236363546990000000000000)
      linear := (-3831480740834508321639951740170260000000000000)
      constant := (110745833125666571148072897294079608496617194705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree106.table
  base := (34875163769755160528174666504982014200493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (342788)
      previous := (171394)
      next := (171394)
      square := (1895237647559536611902020197055000000000000)
      linear := (-212915652590793093473695539365788750000000000)
      constant := (6155669639320168480398558582887872692959685213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20458085472884412747/4000000000000000000)
  centralHi := (127863034205527579669/25000000000000000000)
  directionLo := (32117615741301005227/6250000000000000000)
  directionHi := (513881851860816083633/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree107.table
  base := (7206127758076897675951486323379247994009/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-5432046395158452619974415187224740705000000000000)
      constant := (158552124322852070532604664302973116604713529238445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree107.table
  base := (72061277580758794018694164420837282401399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1207436793584682843526965983209689021250000000000)
      constant := (35251684931675903079058283056486647939796723176431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32117615741301005227/6250000000000000000)
  centralHi := (513881851860816083633/100000000000000000000)
  directionLo := (516300132756036389041/100000000000000000000)
  directionHi := (258150066378018194521/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree108.table
  base := (14881287037963675185355846828317241479551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1218395131069964067156781812306744720000000000000)
      constant := (35909058572613692584592291331445982024821261020595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree108.table
  base := (37203217594905137395738286257162528746213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-609356725457145043959355213131188422500000000000)
      constant := (17963636870530587387355678974323587528451234189997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516300132756036389041/100000000000000000000)
  centralHi := (258150066378018194521/50000000000000000000)
  directionLo := (129676784857559381209/25000000000000000000)
  directionHi := (518707139430237524837/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree109.table
  base := (9598225045833341224390847953895136581969/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-2766754892235611992218310561767980887500000000000)
      constant := (82329220193363522596568627819226142142892741069698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree109.table
  base := (76785800366660285285952132259325498409517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1229990108243897332310454869315064668750000000000)
      constant := (36609318461856458199344908738897417613605179428373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129676784857559381209/25000000000000000000)
  centralHi := (518707139430237524837/100000000000000000000)
  directionLo := (2605515140561933797/500000000000000000)
  directionHi := (521103028112386759401/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree110.table
  base := (39599686555656259723245182542236834893693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-5584241479127609666667724091691572310000000000000)
      constant := (167755154752748259433406122471242479456078109227053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree110.table
  base := (79199373111307393226358524583036478946291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1241266765573504576702199312367752492500000000000)
      constant := (37297819094061733071692086385334574199263172483179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2605515140561933797/500000000000000000)
  centralHi := (521103028112386759401/100000000000000000000)
  directionLo := (261743975728142603877/50000000000000000000)
  directionHi := (104697590291257041551/20000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree111.table
  base := (10205894177969572070040640203534031813793/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-313054065210221963827712614435954602500000000000)
      constant := (9493383704156961797039960301975014177344370822034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree111.table
  base := (40823576711876249648484625810894600094777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-626271711451555910546971877710220158125000000000)
      constant := (18996387818838506072797209660215477830619302087313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261743975728142603877/50000000000000000000)
  centralHi := (104697590291257041551/20000000000000000000)
  directionLo := (131465514663517626953/25000000000000000000)
  directionHi := (525862058654070507813/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree112.table
  base := (84129141304001520744343987378101825604669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-11371409736880762062259860056005586760000000000000)
      constant := (348071392305916741712944848717809064827935762061549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree112.table
  base := (42064570651999139028686433442341029382257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-631910040116359532742844099236564070000000000000)
      constant := (19347094046351166646633841016170469166686724721433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131465514663517626953/25000000000000000000)
  centralHi := (525862058654070507813/100000000000000000000)
  directionLo := (33014093471570507299/6250000000000000000)
  directionHi := (105645099109025623357/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree113.table
  base := (17329067350410263730533828140908010940849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-11472873126193533426722065992316807830000000000000)
      constant := (354439046374295375441765689813990342364432187956645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree113.table
  base := (21661334188012184979489261302046748556211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-318774184390581577469358160381453990937500000000)
      constant := (9850514114784438325700180838066503060876375634659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33014093471570507299/6250000000000000000)
  centralHi := (105645099109025623357/20000000000000000000)
  directionLo := (530578404720636209991/100000000000000000000)
  directionHi := (66322300590079526249/12500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree114.table
  base := (89195739767910938972209195234862390718079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1286037390611811643464919103180892100000000000000)
      constant := (40096086172754128788546455629811739254312029995351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree114.table
  base := (89195739767908888403654554210368308455359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1286373394891933554269177084578503787500000000000)
      constant := (40116380736983343024952186983315695359190762395671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530578404720636209991/100000000000000000000)
  centralHi := (66322300590079526249/12500000000000000000)
  directionLo := (106584185124791250099/20000000000000000000)
  directionHi := (4163444731437158207/781250000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree115.table
  base := (91780350351586082854189692195899168379709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-11675799904819076155646477864939249970000000000000)
      constant := (367348579847392819241785715268750461468445220497389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree115.table
  base := (91780350351584452400374040760063492919777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1297650052221540798660921527631191611250000000000)
      constant := (40837160926239183581714721083714047393091533262313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106584185124791250099/20000000000000000000)
  centralHi := (4163444731437158207/781250000000000000)
  directionLo := (535253194647069231883/100000000000000000000)
  directionHi := (133813298661767307971/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree116.table
  base := (23599792125770743424880973658439672915581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-2944315823532961880027170950312617760000000000000)
      constant := (93472614813028287249011678161748475573104147238701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree116.table
  base := (94399168503081677386543596758040636408891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1308926709551148043052665970683879435000000000000)
      constant := (41564397026905363410118353289123475712292449662579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535253194647069231883/100000000000000000000)
  centralHi := (133813298661767307971/25000000000000000000)
  directionLo := (268787672611623157899/50000000000000000000)
  directionHi := (537575345223246315799/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree117.table
  base := (97052194222408193620715794008333998497677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1319858520382735431618987748617965790000000000000)
      constant := (42276712640994331910458888288139528334672852427413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree117.table
  base := (24263048555601790761809304468219713961321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-330050841720188821861102603434141814687500000000)
      constant := (10574522259745493990704769538929082150572011698249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268787672611623157899/50000000000000000000)
  centralHi := (537575345223246315799/100000000000000000000)
  directionLo := (539887507916132032829/100000000000000000000)
  directionHi := (53988750791613203283/10000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree118.table
  base := (99739427509568556593616886893740783041937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-11980190072757390249033095673872913180000000000000)
      constant := (387148443397901202219482133101067612920595458066177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree118.table
  base := (99739427509567737343848647993977902753763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1331480024210362531836154856789255082500000000000)
      constant := (43038236962469117924904156572509223853227599465947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539887507916132032829/100000000000000000000)
  centralHi := (53988750791613203283/10000000000000000000)
  directionLo := (27109490525270416879/5000000000000000000)
  directionHi := (542189810505408337581/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree119.table
  base := (1024608683645710104328268870360890400787/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-3020413365517540403373825402546033562500000000000)
      constant := (98466137034742669878040835424099585396639871925675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree119.table
  base := (20492173672914071844133451999532981003021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1342756681539969776227899299841942906250000000000)
      constant := (43784840797366887836200787644334969695187521852745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27109490525270416879/5000000000000000000)
  centralHi := (542189810505408337581/100000000000000000000)
  directionLo := (544482378069198557417/100000000000000000000)
  directionHi := (272241189034599278709/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree120.table
  base := (52608258393711280697801389098508677981857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-676839825076829609886528197027519740000000000000)
      constant := (22257707110675461775569720426539081328189674053833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree120.table
  base := (105216516787422043791147318092152918708327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1354033338869577020619643742894630730000000000000)
      constant := (44537900543675385031901037926152514190253172027263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544482378069198557417/100000000000000000000)
  centralHi := (272241189034599278709/50000000000000000000)
  directionLo := (273382666531680802487/50000000000000000000)
  directionHi := (21870613322534464199/4000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree121.table
  base := (27001593194532554134002754127895659152987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-3071145060173926085604928370701644097500000000000)
      constant := (101867745739366248138346242362478603348629234973227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree121.table
  base := (108006372778129805155843590003509106791103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1365309996199184265011388185947318553750000000000)
      constant := (45297416201394708832854145922718714071255753676407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273382666531680802487/50000000000000000000)
  centralHi := (21870613322534464199/4000000000000000000)
  directionLo := (137259698849454673969/25000000000000000000)
  directionHi := (549038795397818695877/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree122.table
  base := (110830436336700939968754934885674933548981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-12386043630008475706881919419117797460000000000000)
      constant := (414361313034891608808923558222327168073056066640101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree122.table
  base := (110830436336700613035550340380649182095763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1376586653528791509403132629000006377500000000000)
      constant := (46063387770524957931484441235692941498656528263947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137259698849454673969/25000000000000000000)
  centralHi := (549038795397818695877/100000000000000000000)
  directionLo := (551302882510047187287/100000000000000000000)
  directionHi := (68912860313755898411/12500000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree123.table
  base := (113688707463141620019773598794213066735903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1387500779924583007927125039492113170000000000000)
      constant := (46812190913826559842845061361375996634488664847607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree123.table
  base := (113688707463141360215953312149560776719133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1387863310858398753794877072052694201250000000000)
      constant := (46835815251066229930802114765797735834856376313477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551302882510047187287/100000000000000000000)
  centralHi := (68912860313755898411/12500000000000000000)
  directionLo := (276778854717934497493/50000000000000000000)
  directionHi := (553557709435868994987/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree124.table
  base := (116581186157459044884954255643471508827241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-12588970408634018435806331291740239600000000000000)
      constant := (428316198526108146981439668294043742045108519273561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree124.table
  base := (116581186157458838440449337411709413690519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1399139968188005998186621515105382025000000000000)
      constant := (47614698643018621003041470289654474033623662737711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276778854717934497493/50000000000000000000)
  centralHi := (553557709435868994987/100000000000000000000)
  directionLo := (555803388877654324311/100000000000000000000)
  directionHi := (69475423609706790539/12500000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree125.table
  base := (119507872419659884925870041828243443765019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-12690433797946789800268537228051460670000000000000)
      constant := (435380753939899784077450406802199384919191987953899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree125.table
  base := (59753936209829860446123696627400507647323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-705208312758806621289182979079034924375000000000)
      constant := (24200018973191112820802257442571099888405479827587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555803388877654324311/100000000000000000000)
  centralHi := (69475423609706790539/12500000000000000000)
  directionLo := (139510007817513783451/25000000000000000000)
  directionHi := (111608006254011026761/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree126.table
  base := (30617191562437670032826927187107584208939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-355330477423876699020298421232296715000000000000)
      constant := (12291760679605966203882113175552867231080307550691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree126.table
  base := (122468766249750549804238305501744168930299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1421693282847220486970110401210757672500000000000)
      constant := (49191833161157136485614620004462862733536333060531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139510007817513783451/25000000000000000000)
  centralHi := (111608006254011026761/20000000000000000000)
  directionLo := (560267744843376812117/100000000000000000000)
  directionHi := (280133872421688406059/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree127.table
  base := (125463867647737831588312821257466491256887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-12893360576572332529192949100673902810000000000000)
      constant := (449684090103853960532625811028381057919810881005127) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree127.table
  base := (627319338238688640240531568396438792769/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-358242485044206932840463711065861374062500000000)
      constant := (12497521071835861050204229948487926780295672773050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560267744843376812117/100000000000000000000)
  centralHi := (280133872421688406059/50000000000000000000)
  directionLo := (562486635684690963251/100000000000000000000)
  directionHi := (140621658921172740813/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree128.table
  base := (3212329415340689901363582630337853372249/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-3248705991471275973413788759246280970000000000000)
      constant := (114230717713504528256693017849175580576343917507290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree128.table
  base := (401541176917585980627011357174962165781/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-361061649376608743938399821829033330000000000000)
      constant := (12698697831235309351013105979313619346885198159120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562486635684690963251/100000000000000000000)
  centralHi := (140621658921172740813/25000000000000000000)
  directionLo := (564696807796786938973/100000000000000000000)
  directionHi := (282348403898393469487/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree129.table
  base := (65778346573713041459533288462638430704737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-727571519733215292117631165183130275000000000000)
      constant := (25789984817572667745112777096154911388423865020553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree129.table
  base := (13155669314742601757931793002455819000989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-727761627418021110072671865184410571875000000000)
      constant := (25802977136975301310640575964925895023151920785705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564696807796786938973/100000000000000000000)
  centralHi := (282348403898393469487/50000000000000000000)
  directionLo := (113379672631010961677/20000000000000000000)
  directionHi := (283449181577527404193/50000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree130.table
  base := (67327208624569626496268573548567375529379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-6598875372255323311289783454803783010000000000000)
      constant := (235787328845362219671587881940158142383442239945459) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree130.table
  base := (67327208624569600545971870173267214567863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-733399956082824732268544086710754483750000000000)
      constant := (26211786567185812135646643165729682058799577048847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113379672631010961677/20000000000000000000)
  centralHi := (283449181577527404193/50000000000000000000)
  directionLo := (569091401762387792987/100000000000000000000)
  directionHi := (142272850440596948247/25000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree131.table
  base := (137786348918772918688759274380326050055727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-13299214133823417987041772845918787090000000000000)
      constant := (478987663777268113563065295964077172262523983640767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree131.table
  base := (2755726978375457549311588976306361423623/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-739038284747628354464416308237098395625000000000)
      constant := (26623823953102192334475196153030092405273150557175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569091401762387792987/100000000000000000000)
  centralHi := (142272850440596948247/25000000000000000000)
  directionLo := (22851040868087512093/4000000000000000000)
  directionHi := (285638010851093901163/50000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree132.table
  base := (140952488156332745254915473347149092914809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1488964169237354372389330975803334240000000000000)
      constant := (54050971663993307117712929400418825743870398042721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree132.table
  base := (70476244078166356257206260642452471342219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-744676613412431976660288529763442307500000000000)
      constant := (27039089294724482021569443483914281177110977875011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22851040868087512093/4000000000000000000)
  centralHi := (285638010851093901163/50000000000000000000)
  directionLo := (286726159594776781591/50000000000000000000)
  directionHi := (573452319189553563183/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree133.table
  base := (144152834961824252782698042671958484162433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-13502140912448960715966184718541229230000000000000)
      constant := (493987901286740094321110295806439097558014872580593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree133.table
  base := (72076417480912113390423114977369733607529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-750314942077235598856160751289786219375000000000)
      constant := (27457582592052720282836086158630815746238684062401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286726159594776781591/50000000000000000000)
  centralHi := (573452319189553563183/100000000000000000000)
  directionLo := (575620388620726928027/100000000000000000000)
  directionHi := (143905097155181732007/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree134.table
  base := (147387389335252818791529470957747978941199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-13603604301761732080428390654852450300000000000000)
      constant := (501575132709669789667401498561256859160942370123679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree134.table
  base := (36846847333813199535636710777182200772871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-377976635371019610526016486408065065625000000000)
      constant := (13939651922543472597051716009714714391852971475199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575620388620726928027/100000000000000000000)
  centralHi := (143905097155181732007/25000000000000000000)
  directionLo := (288890161310434630551/50000000000000000000)
  directionHi := (577780322620869261103/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree135.table
  base := (30131230255324736244279396212981444243567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1522785299008278160543399621240407930000000000000)
      constant := (56580048804969946403258761252235193709264929414115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree135.table
  base := (15065615127662366482422877314825974245291/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-761591599406842843247905194342474043125000000000)
      constant := (28304253053827193842445089094479786695042183820895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288890161310434630551/50000000000000000000)
  centralHi := (577780322620869261103/100000000000000000000)
  directionLo := (115986442418047263853/20000000000000000000)
  directionHi := (289966106045118159633/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree136.table
  base := (153959120785941941709234718139149340648853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-13806531080387274809352802527474892440000000000000)
      constant := (516923820891919928367262831167223198098436953225413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree136.table
  base := (19244890098242741086138486199897745987531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-383614964035823232721888707934408977500000000000)
      constant := (14366215109136751174741866590882940083680021705478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115986442418047263853/20000000000000000000)
  centralHi := (289966106045118159633/50000000000000000000)
  directionLo := (18189879570275523639/3125000000000000000)
  directionHi := (582076146248816756449/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree137.table
  base := (31459259572642513810274923650142897184171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-13907994469700046173815008463786113510000000000000)
      constant := (524685277651241655112165519406242390689986846820455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree137.table
  base := (157296297863212558713337273850123180062303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1545736513472900175279299274790323733750000000000)
      constant := (58327670676851811791980813164909141320304328509207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18189879570275523639/3125000000000000000)
  centralHi := (582076146248816756449/100000000000000000000)
  directionLo := (11684244253589925467/2000000000000000000)
  directionHi := (584212212679496273351/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree138.table
  base := (160667682508440402777016831373524015329513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1556606428779201948697468266677481620000000000000)
      constant := (59167201058077257180111011890364329932624494767697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree138.table
  base := (160667682508440394569007542769989087168623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1557013170802507419671043717843011557500000000000)
      constant := (59196936828568877494504926311269672020432183177287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11684244253589925467/2000000000000000000)
  centralHi := (584212212679496273351/100000000000000000000)
  directionLo := (586340497369806496597/100000000000000000000)
  directionHi := (293170248684903248299/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree139.table
  base := (164073274721630156775253094661346246613111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-14110921248325588902739420336408555650000000000000)
      constant := (540382416506281507638959270279741379503515964381831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree139.table
  base := (164073274721630150258747437573076178469339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1568289828132114664062788160895699381250000000000)
      constant := (60072658891698268557613695222465055938992189058291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586340497369806496597/100000000000000000000)
  centralHi := (293170248684903248299/50000000000000000000)
  directionLo := (588461084752314893503/100000000000000000000)
  directionHi := (9194704449254920211/1562500000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree140.table
  base := (8375653725139321146597205605926868779843/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-3553096159409590066800406568179944180000000000000)
      constant := (137079524650500204840741088929518891310353030306015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree140.table
  base := (83756537251393208879312694230493122523193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-789783242730860954227266301974193602500000000000)
      constant := (30477418433120025002232146412857339254203619299617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588461084752314893503/100000000000000000000)
  centralHi := (9194704449254920211/1562500000000000000)
  directionLo := (590574057743709400179/100000000000000000000)
  directionHi := (29528702887185470009/5000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree141.table
  base := (17098708185191367474351820576599915133099/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-795213779275062868425768456057277655000000000000)
      constant := (30906214211658545550122409819672391072101696668655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree141.table
  base := (170987081851913670636737276681284983668401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1590843142791329152846277047001075028750000000000)
      constant := (61843470752194285181536989807688000833523985619769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590574057743709400179/100000000000000000000)
  centralHi := (29528702887185470009/5000000000000000000)
  directionLo := (148169874445657238211/25000000000000000000)
  directionHi := (118535899556525790569/20000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree142.table
  base := (1363244506007939616274719136458483610887/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 63202500000000000000000000000000000000000000
      center := (859554)
      previous := (429777)
      next := (429777)
      square := (4752380774444817009075081591127500000000000)
      linear := (-714903363234670848845766620975115000000000000)
      constant := (27988677253017311284101221975049179073338695904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree142.table
  base := (17449529676901626762320614289865554461927/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (191012)
      previous := (95506)
      next := (95506)
      square := (1056084616543292668683351464695000000000000)
      linear := (-158908926812233326446937263445126250000000000)
      constant := (6222828858317896826937805377404365071792764715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148169874445657238211/25000000000000000000)
  centralHi := (118535899556525790569/20000000000000000000)
  directionLo := (594777484866288756463/100000000000000000000)
  directionHi := (37173592804143047279/6250000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree143.table
  base := (178037719254098458701439923059257052609921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-14516774805576674360588244081653439930000000000000)
      constant := (572473595561963095143020712552223779502085351929841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree143.table
  base := (7121508770163938244552699086777771385339/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1613396457450543641629765933106450676250000000000)
      constant := (63640106258340362031256317274568785903173796557275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594777484866288756463/100000000000000000000)
  centralHi := (37173592804143047279/6250000000000000000)
  directionLo := (298434048792973446641/50000000000000000000)
  directionHi := (596868097585946893283/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree144.table
  base := (90807174653582188824206584721085438417157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-812124344160524762502802778775814500000000000000)
      constant := (32257865450345579926179282245972639351426035619533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree144.table
  base := (36322869861432875118912760250863319067803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1624673114780150886021510376159138500000000000000)
      constant := (64548107878532322463566307427289132079505064693535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298434048792973446641/50000000000000000000)
  centralHi := (596868097585946893283/100000000000000000000)
  directionLo := (598951413161256759137/100000000000000000000)
  directionHi := (299475706580628379569/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree145.table
  base := (185225186928218062608389454894847518849303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-14719701584202217089512655954275882070000000000000)
      constant := (588867635762613609529029116670310547452731344109863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree145.table
  base := (92612593464109030489142707985667168666681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-817974886054879065206627409605913161875000000000)
      constant := (32731282705068487120582321601373220690661551379089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598951413161256759137/100000000000000000000)
  centralHi := (299475706580628379569/50000000000000000000)
  directionLo := (601027507473547810663/100000000000000000000)
  directionHi := (75128438434193476333/12500000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree146.table
  base := (18887023211726344714133850867230854311099/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-7410582486757494226987430945293551570000000000000)
      constant := (298575884265571554507646154145425520972679318707895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree146.table
  base := (37774046423452689169523040590136335652303/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1647226429439365374804999262264514147500000000000)
      constant := (66383478853154373064246181669781117123605428596035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601027507473547810663/100000000000000000000)
  centralHi := (75128438434193476333/12500000000000000000)
  directionLo := (603096455098075205303/100000000000000000000)
  directionHi := (75387056887259400663/12500000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree147.table
  base := (24068685609288045828433160394927680996701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-414517454522993328289918550747175672500000000000)
      constant := (16819277122550261831019544103133030088257749204938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree147.table
  base := (19254948487430436560075690561379042637063/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-829251543384486309598371852658600985625000000000)
      constant := (33655424103792286621348835065836635966553682468235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603096455098075205303/100000000000000000000)
  centralHi := (75387056887259400663/12500000000000000000)
  directionLo := (151289582333819278077/25000000000000000000)
  directionHi := (605158329335277112309/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree148.table
  base := (196262945199344561313165635273504338644167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-15024091752140531182899273763209545280000000000000)
      constant := (613894259404613036895952557709766061716911720258007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree148.table
  base := (196262945199344560498399984611807477103921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1669779744098579863588488148369889795000000000000)
      constant := (68244673473427627739242575407761995893130151922649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151289582333819278077/25000000000000000000)
  centralHi := (605158329335277112309/100000000000000000000)
  directionLo := (303606601120538380529/50000000000000000000)
  directionHi := (607213202241076761059/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree149.table
  base := (200010613092387679257963829158706310774033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-15125555141453302547361479699520766350000000000000)
      constant := (622352617509554406867293689040718101564841452824193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree149.table
  base := (50002653273096919652854806909584769264277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-420264100357046776995058147855644404687500000000)
      constant := (17296238662670897052795252117406968418731214857813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303606601120538380529/50000000000000000000)
  centralHi := (607213202241076761059/100000000000000000000)
  directionLo := (609261144656264667799/100000000000000000000)
  directionHi := (3046305723281323339/500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree150.table
  base := (50948122138359319795762474114124347290201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-422972736965724275328435712106444095000000000000)
      constant := (17524140297962055259988007063002007482143938203969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree150.table
  base := (203792488553437278670017599734789254185563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1692333058757794352371977034475265442500000000000)
      constant := (70131691739352505050734068706558278311620279440147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609261144656264667799/100000000000000000000)
  centralHi := (3046305723281323339/500000000000000000)
  directionLo := (19103194569843591823/3125000000000000000)
  directionHi := (611302226234994938337/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree151.table
  base := (1621941965488256509553066083031115275461/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-3832120480019711319071472893035802122500000000000)
      constant := (159860889763963056716715326721376262939869682117792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree151.table
  base := (5190214289562420820393002352450425876813/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-425902429021850399190930369381988316562500000000)
      constant := (17771221184858606856003135484986145972202624488970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19103194569843591823/3125000000000000000)
  centralHi := (611302226234994938337/100000000000000000000)
  directionLo := (306668257736214038851/50000000000000000000)
  directionHi := (613336515472428077703/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree152.table
  base := (105729431089784864790577699651020185382149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-7714972654695808320374048754227214780000000000000)
      constant := (324038071248604775593519731225873827866803034808629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree152.table
  base := (105729431089784864629086265759879440625267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-857443186708504420577732960290320545000000000000)
      constant := (36022266825464701654318810211170746252629246390123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306668257736214038851/50000000000000000000)
  centralHi := (613336515472428077703/100000000000000000000)
  directionLo := (615364079731551344023/100000000000000000000)
  directionHi := (76920509966443918003/12500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree153.table
  base := (107671680172329637547670313615713335423817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-862856038816910444733905746931425035000000000000)
      constant := (36487044502817021319359190644575254128904935345073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree153.table
  base := (215343360344659274839087865150133876968121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1726163030746616085547210363633328913750000000000)
      constant := (73010638473837479530046815819843772764048488472449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615364079731551344023/100000000000000000000)
  centralHi := (76920509966443918003/12500000000000000000)
  directionLo := (617384985269206358709/100000000000000000000)
  directionHi := (61738498526920635871/10000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree154.table
  base := (219262066077768697709250081499334495704193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-15632872088017159369672509381076871700000000000000)
      constant := (665515534716343135925219780128937248610310321997553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree154.table
  base := (3425969782465135898530457641624969192183/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-434359922019055832484738701671504184375000000000)
      constant := (18495799802039675449130503321302796090464863642832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617384985269206358709/100000000000000000000)
  centralHi := (61738498526920635871/10000000000000000000)
  directionLo := (309699648630676212393/50000000000000000000)
  directionHi := (619399297261352424787/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree155.table
  base := (44642995875780229771907264895303623585731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-15734335477329930734134715317388092770000000000000)
      constant := (674322343494120209341182845728571969020385162684255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree155.table
  base := (55803744844725287174563082108534974593973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-437179086351457643582674812434676140312500000000)
      constant := (18740553963473278683244765682408541888471910936437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309699648630676212393/50000000000000000000)
  centralHi := (619399297261352424787/100000000000000000000)
  directionLo := (155351769956898201557/25000000000000000000)
  directionHi := (621407079827592806229/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree156.table
  base := (113601050124029852888557328195376988582739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-879766603702372338810940069649961880000000000000)
      constant := (37954845965779888675741274582469900637042654722891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree156.table
  base := (227202100248059705649169042647516351300137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1759993002735437818722443692791392385000000000000)
      constant := (75947688411040761913559732920110067931548309643153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155351769956898201557/25000000000000000000)
  centralHi := (621407079827592806229/100000000000000000000)
  directionLo := (623408396054990080061/100000000000000000000)
  directionHi := (311704198027495040031/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree157.table
  base := (231223428685247373707057974402237559441351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-15937262255955473463059127190010534910000000000000)
      constant := (692110186386096879384703138166567869346033681734871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree157.table
  base := (4624468573704947472111273347418253286821/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-885634830032522531557094067922040104375000000000)
      constant := (38469808439800842946533754076868196353838364568725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623408396054990080061/100000000000000000000)
  centralHi := (311704198027495040031/50000000000000000000)
  directionLo := (78175413502649448341/12500000000000000000)
  directionHi := (625403308021195586729/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree158.table
  base := (235278964690467088049802110976579860669841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-16038725645268244827521333126321755980000000000000)
      constant := (701091220500297233097159719327219588171732615868161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree158.table
  base := (235278964690467087969293868830608613317189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1782546317394652307505932578896768032500000000000)
      constant := (77938001259575928237288775898222855749145796844941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78175413502649448341/12500000000000000000)
  centralHi := (625403308021195586729/100000000000000000000)
  directionLo := (627391876816916969717/100000000000000000000)
  directionHi := (313695938408458484859/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree159.table
  base := (119684354131860858213282336143247087108261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (342788)
      previous := (171394)
      next := (171394)
      square := (1895237647559536611902020197055000000000000)
      linear := (-319215795154088370554636665136525000000000000)
      constant := (14044743675618832774706742406729222316112743701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree159.table
  base := (957474833054886865450822986052233944781/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25205000000000000000000000000000000000000000
      center := (342788)
      previous := (171394)
      next := (171394)
      square := (1895237647559536611902020197055000000000000)
      linear := (-319299212304068983961850662504353125000000000)
      constant := (14051769588993152287689673388890790848048877625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627391876816916969717/100000000000000000000)
  centralHi := (313695938408458484859/50000000000000000000)
  directionLo := (314687081283873405011/50000000000000000000)
  directionHi := (629374162567746810023/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree160.table
  base := (24349265940501406067183267123299225094761/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-8120826211946893778222872499472099060000000000000)
      constant := (359613757032561902713719762035444740520988554857405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree160.table
  base := (60873164851253515155295485738389125519157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-451274908013466699072355366250535920000000000000)
      constant := (19988534438441132378096366038349892255113475857533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314687081283873405011/50000000000000000000)
  centralHi := (629374162567746810023/100000000000000000000)
  directionLo := (63135022445537442193/10000000000000000000)
  directionHi := (631350224455374421931/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree161.table
  base := (49530163622869371751141978266261230975397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-16343115813206558920907950935255419190000000000000)
      constant := (728382773515750730046385841531795115961684536294185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree161.table
  base := (24765081811434685871553702543162850557541/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-908188144691737020340582954027415751875000000000)
      constant := (40485944933989483443926432201198065028547467672145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63135022445537442193/10000000000000000000)
  centralHi := (631350224455374421931/100000000000000000000)
  directionLo := (316660060369100990797/50000000000000000000)
  directionHi := (126664024147640396319/20000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree162.table
  base := (25184318439172278663883886598985371673289/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-913587733473296126965008715087035570000000000000)
      constant := (40977561559917807646669760141478995892107925129205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree162.table
  base := (125921592195861393303488794390175178742561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-913826473356540642536455175553759663750000000000)
      constant := (40998048946803439785352854336264513536459246252809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316660060369100990797/50000000000000000000)
  centralHi := (126664024147640396319/20000000000000000000)
  directionLo := (79410488596423163293/12500000000000000000)
  directionHi := (127056781754277061269/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree163.table
  base := (128034879118572230031264212038637910567903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 637207605000000000000000000000000000000000000000
      center := (8666023428)
      previous := (4333011714)
      next := (4333011714)
      square := (47913502967952645085494972601747455000000000000)
      linear := (-8273021295916050824916181403938930665000000000000)
      constant := (373433758876716780781249993398559107434785532100463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree163.table
  base := (64017439559286115009315016845906123204267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (481445746)
      previous := (240722873)
      next := (240722873)
      square := (2661861275997369171416387366763747500000000000)
      linear := (-459732401010672132366163698540051787812500000000)
      constant := (20756690457662076150072332107877932356799039116123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79410488596423163293/12500000000000000000)
  centralHi := (127056781754277061269/20000000000000000000)
  directionLo := (637241645026318788741/100000000000000000000)
  directionHi := (318620822513159394371/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree164.table
  base := (260330539650614436276628860899672714118621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-16647505981144873014294568744189082400000000000000)
      constant := (756197002540490127713529252939392558329475234662541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree164.table
  base := (130165269825307218128294966781171321450363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-925103130686147886928199618606447487500000000000)
      constant := (42031940839551639093849404226066443133127965191347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (637241645026318788741/100000000000000000000)
  centralHi := (318620822513159394371/50000000000000000000)
  directionLo := (639193385109583212711/100000000000000000000)
  directionHi := (79899173138697901589/12500000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree165.table
  base := (264625528632135215707605178567674875936833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1860996596717516042084086075611144830000000000000)
      constant := (85064951382187839416810592166187990567819588604777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree165.table
  base := (132312764316067607845857005726214081661327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (962891492)
      previous := (481445746)
      next := (481445746)
      square := (5323722551994738342832774733527495000000000000)
      linear := (-930741459350951509124071840132791399375000000000)
      constant := (42553728719485917869699727942185225638125284834263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639193385109583212711/100000000000000000000)
  centralHi := (79899173138697901589/12500000000000000000)
  directionLo := (128227836756274887607/20000000000000000000)
  directionHi := (160284795945343609509/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree166.table
  base := (2101208790482103465384110868915488920189/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-4212608189942603935804745154202881135000000000000)
      constant := (193757549362758788574388109447777870767821080559008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree166.table
  base := (268954725181709243556564722464817371039881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1872759576031510262639888123318270622500000000000)
      constant := (86157489110254011880033794969982501153529170699889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128227836756274887607/20000000000000000000)
  centralHi := (160284795945343609509/25000000000000000000)
  directionLo := (643079094973430231891/100000000000000000000)
  directionHi := (160769773743357557973/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree167.table
  base := (34164766162417363927214360052028585416571/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318603802500000000000000000000000000000000000000
      center := (4333011714)
      previous := (2166505857)
      next := (2166505857)
      square := (23956751483976322542747486300873727500000000000)
      linear := (-4237974037270796776920296638280686402500000000000)
      constant := (196133476893631057783971532771021758888807453688982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree167.table
  base := (273318129299338911407722458146083682007933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1884036233361117507031632566370958446250000000000)
      constant := (87213976692949840474447177115354686838929278120677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643079094973430231891/100000000000000000000)
  centralHi := (160769773743357557973/25000000000000000000)
  directionLo := (322506585903235925311/50000000000000000000)
  directionHi := (645013171806471850623/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree168.table
  base := (277715740985026558654794152557921121562199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1894817726488439830238154721048218520000000000000)
      constant := (88232854756684231489243029679294018969990281851631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree168.table
  base := (277715740985026558646870875947441179972529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1895312890690724751423377009423646270000000000000)
      constant := (88276920187059354648962801794534309013470425997401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell172.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322506585903235925311/50000000000000000000)
  centralHi := (645013171806471850623/100000000000000000000)
  directionLo := (32347073330358816479/5000000000000000000)
  directionHi := (646941466607176329581/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree169.table
  base := (282147560238774473978612781332450671115459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1274415210000000000000000000000000000000000000000
      center := (17332046856)
      previous := (8666023428)
      next := (8666023428)
      square := (95827005935905290170989945203494910000000000000)
      linear := (-17154822927708729836605598425745187750000000000000)
      constant := (803715553157937002774636681973901817611924861573139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 31883
  qDenominator := 60208
  table := BinomialMassData.Q31883_60208.Degree169.table
  base := (56429512047754894794466082384851366007169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (1925782984)
      previous := (962891492)
      next := (962891492)
      square := (10647445103989476685665549467054990000000000000)
      linear := (-1906589548020331995815121452476334093750000000000)
      constant := (89346319592582586811935676398219057260016528757805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q31883_60208.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell172.Kernel169
