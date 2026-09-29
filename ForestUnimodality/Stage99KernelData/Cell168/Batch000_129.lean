import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell168.Parameters
import ForestUnimodality.BinomialMassData.Q107_187.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_187.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_187.Batch100_149
import ForestUnimodality.BinomialMassData.Q27_47.Batch000_049
import ForestUnimodality.BinomialMassData.Q27_47.Batch050_099
import ForestUnimodality.BinomialMassData.Q27_47.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree000.table
  base := (387835858430363134918650309/20000000000000000000000000)
  polynomial :=
    { denominator := 935000000000000000000000000000000000000000
      center := (2461)
      previous := (0)
      next := (1840)
      square := (60463900039238935579799516310000000000000)
      linear := (-208219068341286785428501109100000000000000)
      constant := (18131326381619476557446901945750000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree000.table
  base := (387835858430363134918650309/20000000000000000000000000)
  polynomial :=
    { denominator := 235000000000000000000000000000000000000000
      center := (621)
      previous := (0)
      next := (460)
      square := (15196809100771283274067258110000000000000)
      linear := (-52333134823745876551548407100000000000000)
      constant := (4557071336556766835294141130750000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree001.table
  base := (118075706767319277447405123118692094884117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-103752480776435522178413607784080000000000000)
      constant := (4180952026630773415872127968029683866002687373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree001.table
  base := (117778476025261202769394857617724976895723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-6560570056315410989444814143280000000000000)
      constant := (263470067238772030230389408978494473962652107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49442340589881917683/100000000000000000000)
  directionHi := (12360585147470479421/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree002.table
  base := (2967736899799348710142008117460201818021/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-129631029993229786606567800764760000000000000)
      constant := (2713202576714557293215771442560404934359408725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree002.table
  base := (73853409778465897662490196669577187301419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-8201825439198709583044078019160000000000000)
      constant := (170679858435546746520058290480056006748834571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49442340589881917683/100000000000000000000)
  centralHi := (12360585147470479421/25000000000000000000)
  directionLo := (69922028617680780441/100000000000000000000)
  directionHi := (34961014308840390221/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree003.table
  base := (24091202464116884026303768412551647752043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-77754789605012025517360996872720000000000000)
      constant := (942600482172332413932900745190948570241191667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree003.table
  base := (47885262977592869616246849477513335515319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-9843080822082008176643341895040000000000000)
      constant := (118499333525339284794753123103886958153339671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69922028617680780441/100000000000000000000)
  centralHi := (34961014308840390221/50000000000000000000)
  directionLo := (42818322973400228229/50000000000000000000)
  directionHi := (85636645946800456459/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree004.table
  base := (2017561098245583303722953311997662381027/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-90694064213409157731438093363060000000000000)
      constant := (712764562081271010403453952390690046417065304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree004.table
  base := (16022437788842313662769889313664767065411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-5742168102482653385121302885460000000000000)
      constant := (44816938984419273380726349601005470447492899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42818322973400228229/50000000000000000000)
  centralHi := (85636645946800456459/100000000000000000000)
  directionLo := (49442340589881917683/50000000000000000000)
  directionHi := (98884681179763835367/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree005.table
  base := (22187213621808564558393192385620912786491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-207266677643612579891030379706800000000000000)
      constant := (1183752977749956322753922239888277699230803779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree005.table
  base := (22006613039645225719073640659013212712613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-13125591587848605363841869646800000000000000)
      constant := (74528165069181589757665605071260186882162117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49442340589881917683/50000000000000000000)
  centralHi := (98884681179763835367/100000000000000000000)
  directionLo := (22111286905134603747/20000000000000000000)
  directionHi := (6909777157854563671/6250000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree006.table
  base := (15134875570566487822221694492788714289/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-116572613430203422159592286343740000000000000)
      constant := (537921000422905699902737820823304217585684992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree006.table
  base := (15361523358652830775129381312878765169867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-14766846970731903957441133522680000000000000)
      constant := (67860819847716982429414449851989192260236203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22111286905134603747/20000000000000000000)
  centralHi := (6909777157854563671/6250000000000000000)
  directionLo := (121108506134108144629/100000000000000000000)
  directionHi := (12110850613410814463/10000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree007.table
  base := (10855729362557053659828214071790561308617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-259023776077201108747338765668160000000000000)
      constant := (1054310211362666519876257516200504138401027873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree007.table
  base := (430085556128721194383073467399551665949/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-16408102353615202551040397398560000000000000)
      constant := (66633196306484612267905701480400240752033525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121108506134108144629/100000000000000000000)
  centralHi := (12110850613410814463/10000000000000000000)
  directionLo := (130812137437782107019/100000000000000000000)
  directionHi := (6540606871889105351/5000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree008.table
  base := (7481395219982954864204256832575030924319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-284902325293995373175492958648840000000000000)
      constant := (1091928342246281692155567298020876256392511111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree008.table
  base := (740204653641028516990069394042394384603/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-9024678868249250572319830637220000000000000)
      constant := (34565098913002460633691516952078245977940135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130812137437782107019/100000000000000000000)
  centralHi := (6540606871889105351/5000000000000000000)
  directionLo := (69922028617680780441/50000000000000000000)
  directionHi := (139844057235361560883/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree009.table
  base := (1230061252610442572690753199863575499703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-155390437255394818801823575814760000000000000)
      constant := (586395107101412651667311169317328743298228414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree009.table
  base := (4858690640501933886426609959220100625989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-19690613119381799738238925150320000000000000)
      constant := (74352129046717502259185823171257202282809701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69922028617680780441/50000000000000000000)
  centralHi := (139844057235361560883/100000000000000000000)
  directionLo := (148327021769645753049/100000000000000000000)
  directionHi := (2966540435392915061/2000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree010.table
  base := (580093092683113949739183142997051643797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-336659423727583902031801344610200000000000000)
      constant := (1287390788975555852571037884585319494659686465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree010.table
  base := (2852111982047876029051449571520751959453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-21331868502265098331838189026200000000000000)
      constant := (81702650021942129387266243691489341078431677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148327021769645753049/100000000000000000000)
  centralHi := (2966540435392915061/2000000000000000000)
  directionLo := (9771900569613742413/6250000000000000000)
  directionHi := (156350409113819878609/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree011.table
  base := (251052456492620453872766423527297707347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (83674)
      previous := (0)
      next := (62560)
      square := (2055772601334123809713183554540000000000000)
      linear := (-32957997540398015132723230690080000000000000)
      constant := (129990676073838112249315643441506397058280565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree011.table
  base := (608432428346259139745747598066871321427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-11486561942574198462718726451040000000000000)
      constant := (45408145595378648505767781663999718749032243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9771900569613742413/6250000000000000000)
  centralHi := (156350409113819878609/100000000000000000000)
  directionLo := (81990846246798695873/50000000000000000000)
  directionHi := (163981692493597391747/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree012.table
  base := (-15096429228341546673082009969553373771/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-194208261080586215444054865285780000000000000)
      constant := (798312091888685343020317989679178752290407604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree012.table
  base := (-151521665163877979099356412634876473117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-24614379268031695519036716777960000000000000)
      constant := (101462276269677182527380740011049557870884547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81990846246798695873/50000000000000000000)
  centralHi := (163981692493597391747/100000000000000000000)
  directionLo := (42818322973400228229/25000000000000000000)
  directionHi := (171273291893600912917/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree013.table
  base := (-64816540225731032759390063445067481437/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-207147535688983347658131961776120000000000000)
      constant := (892584415126288530549467770602524352416295470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree013.table
  base := (-1321105683318324671370080293110681611891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-26255634650914994112635980653840000000000000)
      constant := (113490264916250186593252187880978504319332781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42818322973400228229/25000000000000000000)
  centralHi := (171273291893600912917/100000000000000000000)
  directionLo := (89133447087886858531/50000000000000000000)
  directionHi := (178266894175773717063/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree014.table
  base := (-2317563256726074684301516356484566664097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-440173620594760959744418116532920000000000000)
      constant := (1993917646858686327003769744962731188323192007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree014.table
  base := (-584400387526070190511496426132980637081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-13948445016899146353117622264860000000000000)
      constant := (63399637063085849178035849392064491545376142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89133447087886858531/50000000000000000000)
  centralHi := (178266894175773717063/100000000000000000000)
  directionLo := (184996298887524747749/100000000000000000000)
  directionHi := (739985195550098991/400000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree015.table
  base := (-3216353369175061277557461919273094494541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-466052169811555224172572309513600000000000000)
      constant := (2221755661762649778137352251922439158620395771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree015.table
  base := (-129303824243203983066483630609177877621/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-29538145416681591299834508405600000000000000)
      constant := (141319529673148315319732417697108151708380275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184996298887524747749/100000000000000000000)
  centralHi := (739985195550098991/400000000000000000)
  directionLo := (95744680851063829787/50000000000000000000)
  directionHi := (7659574468085106383/4000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree016.table
  base := (-4015281379087253218461608644797788820703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-491930719028349488600726502494280000000000000)
      constant := (2467893266648922862933262773111906122728836793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree016.table
  base := (-402845788559335256406752701377096187409/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-15589700399782444946716886140740000000000000)
      constant := (78500808075653126076863306525609972610067595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95744680851063829787/50000000000000000000)
  centralHi := (7659574468085106383/4000000000000000000)
  directionLo := (49442340589881917683/25000000000000000000)
  directionHi := (197769362359527670733/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree017.table
  base := (-4730671323733861104357233002060706618371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (54142)
      previous := (0)
      next := (40480)
      square := (1330205800863256582755589358820000000000000)
      linear := (-30459368720302573707581217380880000000000000)
      constant := (160691742721068742236059074922741126486010853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree017.table
  base := (-1185339962439643158812135738094639648859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-16410328091224094243516518078680000000000000)
      constant := (86904905401521752828842830952527882031340938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49442340589881917683/25000000000000000000)
  centralHi := (197769362359527670733/100000000000000000000)
  directionLo := (101927996314923268079/50000000000000000000)
  directionHi := (203855992629846536159/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree018.table
  base := (-5374521036353285310110996332647858809233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-543687817461938017457034888455640000000000000)
      constant := (3012935188359873420667864473192597025299931223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree018.table
  base := (-1345796271204753915346936545171258872531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-17230955782665743540316150016620000000000000)
      constant := (95858931393174361806083592035513378301158042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101927996314923268079/50000000000000000000)
  centralHi := (203855992629846536159/100000000000000000000)
  directionLo := (209766085853042341323/100000000000000000000)
  directionHi := (52441521463260585331/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree019.table
  base := (-1488940600157150102523184140329735722157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-284783183339366140942594540718160000000000000)
      constant := (1655553806956761918053352254619488943063783734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree019.table
  base := (-745347178750332161327157343668239314653/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-18051583474107392837115781954560000000000000)
      constant := (105353118030183653905223660969617437415726092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209766085853042341323/100000000000000000000)
  centralHi := (52441521463260585331/25000000000000000000)
  directionLo := (215514166163414453401/100000000000000000000)
  directionHi := (107757083081707226701/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree020.table
  base := (-6481109526309694904292137437967450324219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-595444915895526546313343274417000000000000000)
      constant := (3626042117215276013373385130775716229612385789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree020.table
  base := (-648678150934330693057459014373842091207/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-18872211165549042133915413892500000000000000)
      constant := (115380126325304286635527408528240914102618685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215514166163414453401/100000000000000000000)
  centralHi := (107757083081707226701/50000000000000000000)
  directionLo := (221112869051346037471/100000000000000000000)
  directionHi := (6909777157854563671/3125000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree021.table
  base := (-1391129151441436967987046627409936773699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-621323465112320810741497467397680000000000000)
      constant := (3957560938815416519912459148756249604802598345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree021.table
  base := (-870028105250867059439279349904182191579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-19692838856990691430715045830440000000000000)
      constant := (125934403383617444039790745607516646155207956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221112869051346037471/100000000000000000000)
  centralHi := (6909777157854563671/3125000000000000000)
  directionLo := (11328663414446073273/5000000000000000000)
  directionHi := (226573268288921465461/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree022.table
  base := (-1845809993813287104400750797232395896097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (41837)
      previous := (0)
      next := (31280)
      square := (1027886300667061904856591777270000000000000)
      linear := (-29418273378596139780438711835380000000000000)
      constant := (195705853990075568778536831362876426892615274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree022.table
  base := (-1477386182783680228656929613897460465707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-41026933096864681455029355536760000000000000)
      constant := (274023452329838247059800106538662549156266185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11328663414446073273/5000000000000000000)
  centralHi := (226573268288921465461/100000000000000000000)
  directionLo := (115952566752669893569/50000000000000000000)
  directionHi := (231905133505339787139/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree023.table
  base := (-7766847911216436085873313233401959885309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-673080563545909339597805853359040000000000000)
      constant := (4669842305164758061683119170898826864770629579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree023.table
  base := (-7769818266545187960971202879527930132379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-42668188479747980048628619412640000000000000)
      constant := (297217742280316971368879074235982802337574789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115952566752669893569/50000000000000000000)
  centralHi := (231905133505339787139/100000000000000000000)
  directionLo := (237117135587319701757/100000000000000000000)
  directionHi := (118558567793659850879/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree024.table
  base := (-810873380439759570518969658270592487069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-349479556381351802012980023169860000000000000)
      constant := (2525211156390301153723267937553598256598420695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree024.table
  base := (-1622224111265661719911786287543516705779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-44309443862631278642227883288520000000000000)
      constant := (321446742471592866225612458158721857984670945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237117135587319701757/100000000000000000000)
  centralHi := (118558567793659850879/50000000000000000000)
  directionLo := (242217012268216289259/100000000000000000000)
  directionHi := (12110850613410814463/5000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree025.table
  base := (-8410635534156272140607329858111871582269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-724837661979497868454114239320400000000000000)
      constant := (5447208038725867829131945931339185962639635339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree025.table
  base := (-4206275239810180115922025620940427559629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-22975349622757288617913573582200000000000000)
      constant := (173353334778711522237646706927092595520779539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242217012268216289259/100000000000000000000)
  centralHi := (12110850613410814463/5000000000000000000)
  directionLo := (49442340589881917683/20000000000000000000)
  directionHi := (3862682858584524819/1562500000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree026.table
  base := (-8673888814174452061003979498357262394659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-750716211196292132882268432301080000000000000)
      constant := (5860152774428809234915362724998584891321169429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree026.table
  base := (-1084427877615647356570447773913206397087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-23795977314198937914713205520140000000000000)
      constant := (186497309368519266202773932182422908275339268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49442340589881917683/20000000000000000000)
  centralHi := (3862682858584524819/1562500000000000000)
  directionLo := (126053729732754249047/50000000000000000000)
  directionHi := (50421491893101699619/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree027.table
  base := (-4449760628771264204777365230142666882909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-388297380206543198655211312640880000000000000)
      constant := (3144610292643634286983448355114771081771555179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree027.table
  base := (-8900748754229129242343124480413474648147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-49233210011281174423025674916160000000000000)
      constant := (400308357652503450215973858861226634502243277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126053729732754249047/50000000000000000000)
  centralHi := (50421491893101699619/20000000000000000000)
  directionLo := (128454968920200684687/50000000000000000000)
  directionHi := (411055900544642191/160000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree028.table
  base := (-181766479770757847297668252222122626411/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-401236654814940330869288409131220000000000000)
      constant := (3367191903238194877080625590202794846925843525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree028.table
  base := (-9089304826122812751542716999660217361499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-50874465394164473016624938792040000000000000)
      constant := (428646169586999159523626071434310579848448709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128454968920200684687/50000000000000000000)
  centralHi := (411055900544642191/160000000000000000)
  directionLo := (261624274875564214039/100000000000000000000)
  directionHi := (6540606871889105351/2500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree029.table
  base := (-369636254523215253700094166451000437359/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-828351858846674926166731011243120000000000000)
      constant := (7195621129429011980915375530335314142649828225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree029.table
  base := (-4620844576496345950358071172142611570063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-26257860388523885805112101333960000000000000)
      constant := (229003366871613982310300598165606971041730833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261624274875564214039/100000000000000000000)
  centralHi := (6540606871889105351/2500000000000000000)
  directionLo := (66563788131747479379/25000000000000000000)
  directionHi := (266255152526989917517/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree030.table
  base := (-9357737893233011322641486381788995109129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-854230408063469190594885204223800000000000000)
      constant := (7672916135777803648416609293403220630028867999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree030.table
  base := (-187167238154331277537524914951751957301/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-27078488079965535101911733271900000000000000)
      constant := (244194516799651405760393929215789498158052275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66563788131747479379/25000000000000000000)
  centralHi := (266255152526989917517/100000000000000000000)
  directionLo := (135403426184658036587/50000000000000000000)
  directionHi := (10832274094772642927/4000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree031.table
  base := (-9439180428802340985724817235193865987683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-880108957280263455023039397204480000000000000)
      constant := (8166256171996879206169205335167045700276713173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree031.table
  base := (-9439677334515512179330331642686597046097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-55798231542814368797422730419680000000000000)
      constant := (519792286629739326774216222242645307125171727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135403426184658036587/50000000000000000000)
  centralHi := (10832274094772642927/4000000000000000000)
  directionLo := (137641650975624412817/50000000000000000000)
  directionHi := (55056660390249765127/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree032.table
  base := (-9485512893396511683440359637418577831479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-905987506497057719451193590185160000000000000)
      constant := (8675631484406585559245985531969669751811010849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree032.table
  base := (-1185738522271155676706676563229452715049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-28719743462848833695510997147780000000000000)
      constant := (276107945170659567035585542602184555809827036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137641650975624412817/50000000000000000000)
  centralHi := (55056660390249765127/20000000000000000000)
  directionLo := (55937622894144624353/20000000000000000000)
  directionHi := (139844057235361560883/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree033.table
  base := (-9496950315621434241820013833915259619433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (83674)
      previous := (0)
      next := (62560)
      square := (2055772601334123809713183554540000000000000)
      linear := (-84715095973986543989031616651440000000000000)
      constant := (836457686697418419270130942193443389669822493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree033.table
  base := (-9497264459169154795472352233850848788437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-59080742308580965984621258171440000000000000)
      constant := (585659380798776750216332704968683475026342667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55937622894144624353/20000000000000000000)
  centralHi := (139844057235361560883/50000000000000000000)
  directionLo := (7100615572751166653/2500000000000000000)
  directionHi := (284024622910046666121/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree034.table
  base := (-1894731696191517551281741379247513316431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (54142)
      previous := (0)
      next := (40480)
      square := (1330205800863256582755589358820000000000000)
      linear := (-56337917937096838135735410361560000000000000)
      constant := (573085857790556675932556428051559325540507165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree034.table
  base := (-9473907912660158424294167656466074279011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-60721997691464264578220522047320000000000000)
      constant := (620122400729177051127890081358706441917664701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7100615572751166653/2500000000000000000)
  centralHi := (284024622910046666121/100000000000000000000)
  directionLo := (72073977387039669733/25000000000000000000)
  directionHi := (288295909548158678933/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree035.table
  base := (-1176970652174807353397998294888512026829/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-491811577073720256367828084563600000000000000)
      constant := (5149951050346531981488713705236924491735266796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree035.table
  base := (-9415963097642272758884939566070579290749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-62363253074347563171819785923200000000000000)
      constant := (655604674981689000448428941904050090346735459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72073977387039669733/25000000000000000000)
  centralHi := (288295909548158678933/100000000000000000000)
  directionLo := (292504831592925957867/100000000000000000000)
  directionHi := (73126207898231489467/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree036.table
  base := (-4661684545569732030234142364600640901369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-504750851682117388581905181053940000000000000)
      constant := (5436679330835558252518427811297000188320027439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree036.table
  base := (-1864705189401049035100480020985414053517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-64004508457230861765419049799080000000000000)
      constant := (692105991640559146223795956302456101778904735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292504831592925957867/100000000000000000000)
  centralHi := (73126207898231489467/25000000000000000000)
  directionLo := (148327021769645753049/50000000000000000000)
  directionHi := (296654043539291506099/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree037.table
  base := (-287392065883210516304544960410583762557/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-517690126290514520795982277544280000000000000)
      constant := (5731413303758467502932419813371866742514308272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree037.table
  base := (-459833517470138459865809044881214447299/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-32822881920057080179509156837480000000000000)
      constant := (364813093742875739730654704147603972859165090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148327021769645753049/50000000000000000000)
  centralHi := (296654043539291506099/100000000000000000000)
  directionLo := (300746016750376505441/100000000000000000000)
  directionHi := (150373008375188252721/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree038.table
  base := (-4517677440258765122102354737469635059469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-530629400898911653010059374034620000000000000)
      constant := (6034151944318129900587392075688304331605428539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree038.table
  base := (-2258863304204073416539873647925498458787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-33643509611498729476308788775420000000000000)
      constant := (384082568399349489834679865571945147809079034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300746016750376505441/100000000000000000000)
  centralHi := (150373008375188252721/50000000000000000000)
  directionLo := (304783056671829496569/100000000000000000000)
  directionHi := (30478305667182949657/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree039.table
  base := (-353593624306494364377623661885122271471/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1087137351014617570448272941049920000000000000)
      constant := (12689788924438735419041211315086618982223265025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree039.table
  base := (-8839918386639240552286569326655046088169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-68928274605880757546216841426720000000000000)
      constant := (807722742742599577715655334888359003191234679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304783056671829496569/100000000000000000000)
  centralHi := (30478305667182949657/10000000000000000000)
  directionLo := (308767318019944454771/100000000000000000000)
  directionHi := (77191829504986113693/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree040.table
  base := (-8610038147737613022535970436975041060213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1113015900231411834876427134030600000000000000)
      constant := (13327280495973547464873277695269419789165411603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree040.table
  base := (-2152524906640170050193539169542102103777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-35284764994382028069908052651300000000000000)
      constant := (424149465362314058603960837648962992905513214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308767318019944454771/100000000000000000000)
  centralHi := (77191829504986113693/25000000000000000000)
  directionLo := (9771900569613742413/3125000000000000000)
  directionHi := (312700818227639757217/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree041.table
  base := (-8345974384296126175621233712575773844579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1138894449448206099304581327011280000000000000)
      constant := (13980777663149736879806375769056277764428916949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree041.table
  base := (-166920458973335659110467241824518762357/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-36105392685823677366707684589240000000000000)
      constant := (444946821642043123928240605222310951348834675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9771900569613742413/3125000000000000000)
  centralHi := (312700818227639757217/100000000000000000000)
  directionLo := (158292724693241418133/50000000000000000000)
  directionHi := (316585449386482836267/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree042.table
  base := (-160953401033040760670972253957197950847/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-582386499332500181866367759995980000000000000)
      constant := (7325139850454536260447043929640348621420781425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree042.table
  base := (-804770839163043622682661654397189959947/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-36926020377265326663507316527180000000000000)
      constant := (466253418077772780685998980148863036892385385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158292724693241418133/50000000000000000000)
  centralHi := (316585449386482836267/100000000000000000000)
  directionLo := (64084597777078127079/20000000000000000000)
  directionHi := (80105747221347658849/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree043.table
  base := (-771514114227704624541392210317211449339/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-595325773940897314080444856486320000000000000)
      constant := (7667893025005405796522591210668317164140322545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree043.table
  base := (-7715171393290381778451357951209327236103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-75493296137413951920613896930240000000000000)
      constant := (976138475236820277198309654503438596135448473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64084597777078127079/20000000000000000000)
  centralHi := (80105747221347658849/25000000000000000000)
  directionLo := (324215108915752190737/100000000000000000000)
  directionHi := (162107554457876095369/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree044.table
  base := (-7348399992025728701059104184911789329659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (83674)
      previous := (0)
      next := (62560)
      square := (2055772601334123809713183554540000000000000)
      linear := (-110593645190780808417185809632120000000000000)
      constant := (1457936025371132305639070597860005421721014039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree044.table
  base := (-293936953911358159586475563272659185767/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-77134551520297250514213160806120000000000000)
      constant := (1020788534253761023691621448245307396466017425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (324215108915752190737/100000000000000000000)
  centralHi := (162107554457876095369/50000000000000000000)
  directionLo := (81990846246798695873/25000000000000000000)
  directionHi := (327963384987194783493/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree045.table
  base := (-6947456116952041862940933516949568123001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1242408646315383157017198098934000000000000000)
      constant := (16754810055357113024312219374577290552306778031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree045.table
  base := (-1736868729935331453873741320786447417731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-39387903451590274553906212341000000000000000)
      constant := (533228496480849874397128574480515475308464442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81990846246798695873/25000000000000000000)
  centralHi := (327963384987194783493/100000000000000000000)
  directionLo := (331669303577019056207/100000000000000000000)
  directionHi := (20729331473563691013/6250000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree046.table
  base := (-3256158429292798480569110690390317122339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-634143597766088710722676145957340000000000000)
      constant := (8744163561054417802393942431992861000548927509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree046.table
  base := (-1302466334275542284395719955217947879421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-80417062286063847701411688557880000000000000)
      constant := (1113143835760203044413460875445657765671795055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331669303577019056207/100000000000000000000)
  centralHi := (20729331473563691013/6250000000000000000)
  directionLo := (41916783627330948341/12500000000000000000)
  directionHi := (335334269018647586729/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree047.table
  base := (-6042987881514339010719059987709899363137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1294165744748971685873506484895360000000000000)
      constant := (18237847281252647254224856928148232529170462247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree047.table
  base := (-6042999545483963451519093502029051166323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (1242)
      previous := (0)
      next := (920)
      square := (30393618201542566548134516220000000000000)
      linear := (-1745921652530790346702360690080000000000000)
      constant := (24698915970769062065152278913184634595182819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41916783627330948341/12500000000000000000)
  centralHi := (335334269018647586729/100000000000000000000)
  directionLo := (338959609719619242637/100000000000000000000)
  directionHi := (169479804859809621319/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree048.table
  base := (-553947355708142982931436979906979736749/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-660022146982882975150830338938020000000000000)
      constant := (9501685189963524473511199954726244127928121095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree048.table
  base := (-5539482737432020916416117076223481589169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-83699573051830444888610216309640000000000000)
      constant := (1209572628291951753462175876993982329169525679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338959609719619242637/100000000000000000000)
  centralHi := (169479804859809621319/50000000000000000000)
  directionLo := (42818322973400228229/12500000000000000000)
  directionHi := (342546583787201825833/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree049.table
  base := (-5001777259264455714666758516975188332507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1345922843182560214729814870856720000000000000)
      constant := (19784896300147418467934752559163234639200562717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree049.table
  base := (-5001784481700245165913088844974807349343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-85340828434713743482209480185520000000000000)
      constant := (1259314561612657853393038468541590650565301313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42818322973400228229/12500000000000000000)
  centralHi := (342546583787201825833/100000000000000000000)
  directionLo := (346096384129173423781/100000000000000000000)
  directionHi := (173048192064586711891/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree050.table
  base := (-276868849552353167026787043601534242239/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-685900696199677239578984531918700000000000000)
      constant := (10291212475413702814009128635588383592665155272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree050.table
  base := (-4429907272562008964197958369786664000591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-86982083817597042075808744061400000000000000)
      constant := (1310074845078414336418653702981141259222694481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346096384129173423781/100000000000000000000)
  centralHi := (173048192064586711891/50000000000000000000)
  directionLo := (174805071544201951103/50000000000000000000)
  directionHi := (349610143088403902207/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree051.table
  base := (-3823848569316653742707775081186498865723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (54142)
      previous := (0)
      next := (40480)
      square := (1330205800863256582755589358820000000000000)
      linear := (-82216467153891102563889603342240000000000000)
      constant := (1258585662448607061510551811445419371833207789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree051.table
  base := (-764770606813315207636184759442081788799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-88623339200480340669408007937280000000000000)
      constant := (1361853474438996378966276952606902206642715045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174805071544201951103/50000000000000000000)
  centralHi := (349610143088403902207/100000000000000000000)
  directionLo := (70617787332456158119/20000000000000000000)
  directionHi := (88272234165570197649/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree052.table
  base := (-3183619742637499282705277489688888459899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1423558490832943008014277449798760000000000000)
      constant := (22225490178204572535481162345704829259445791869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree052.table
  base := (-1591811625482270964553288770368138384517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-45132297291681819631503635906580000000000000)
      constant := (707325223207294957742649456388736782308601947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70617787332456158119/20000000000000000000)
  centralHi := (88272234165570197649/25000000000000000000)
  directionLo := (89133447087886858531/25000000000000000000)
  directionHi := (2852270306812379473/800000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree053.table
  base := (-125460815689293711210343915546265066167/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-724718520024868636221215821389720000000000000)
      constant := (11535513329282447305552992520066056569012061770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree053.table
  base := (-501843813910476855268351702753900659639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-91905849966246937856606535689040000000000000)
      constant := (1468465758473026026870358236333143167214287245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89133447087886858531/25000000000000000000)
  centralHi := (2852270306812379473/800000000000000000)
  directionLo := (44993209084696865271/12500000000000000000)
  directionHi := (359945672677574922169/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree054.table
  base := (-1800639211483222336320432300915126054209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1475315589266531536870585835760120000000000000)
      constant := (23932565670230826105391916304890738957010365479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree054.table
  base := (-450160343837081793564224410655846903777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-46773552674565118225102899782460000000000000)
      constant := (761649704329097478048495320678842468379113214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44993209084696865271/12500000000000000000)
  centralHi := (359945672677574922169/100000000000000000000)
  directionLo := (363325518402324433889/100000000000000000000)
  directionHi := (36332551840232443389/10000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree055.table
  base := (-1057889154409673533369192237108839301607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (83674)
      previous := (0)
      next := (62560)
      square := (2055772601334123809713183554540000000000000)
      linear := (-136472194407575072845340002612800000000000000)
      constant := (2255464289824621959578635119418730999860191347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree055.table
  base := (-1057890852923323385245051916131031298981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-95188360732013535043805063440800000000000000)
      constant := (1579151395457879468513069864962766551860550971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363325518402324433889/100000000000000000000)
  centralHi := (36332551840232443389/10000000000000000000)
  directionLo := (183337105740575382761/50000000000000000000)
  directionHi := (366674211481150765523/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree056.table
  base := (-280966699189493677332638036653122936221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1527072687700120065726894221721480000000000000)
      constant := (25703651192620347008097634633055316944043287851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree056.table
  base := (-280968031987576947761271764593322143427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-96829616114896833637404327316680000000000000)
      constant := (1636021717701949723397648700747853351385169757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183337105740575382761/50000000000000000000)
  centralHi := (366674211481150765523/100000000000000000000)
  directionLo := (369992597775049495499/100000000000000000000)
  directionHi := (739985195550098991/200000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree057.table
  base := (530127722602438990336946958161309403899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1552951236916914330155048414702160000000000000)
      constant := (26613197668787600546364516367042002828544944131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree057.table
  base := (53012667710921951965640087788219366691/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-49235435748890066115501795596280000000000000)
      constant := (846955187241971624878188307040250882905102095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369992597775049495499/100000000000000000000)
  centralHi := (739985195550098991/200000000000000000)
  directionLo := (373281485545875213453/100000000000000000000)
  directionHi := (186640742772937606727/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree058.table
  base := (1375393775900436015568178421946856614051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1578829786133708594583202607682840000000000000)
      constant := (27538746604855690110615209277091619628936749419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree058.table
  base := (171924119503935029863409955708894006339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-50056063440331715412301427534220000000000000)
      constant := (876408682550328369302714594389523787440011404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373281485545875213453/100000000000000000000)
  centralHi := (186640742772937606727/50000000000000000000)
  directionLo := (75308329551077238303/20000000000000000000)
  directionHi := (94135411938846547879/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree059.table
  base := (450966240027298041535806716141456953331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1604708335350502859011356800663520000000000000)
      constant := (28480297991712813057398753708820293041005158695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree059.table
  base := (281853819673956939003546396871615508003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-50876691131773364709101059472160000000000000)
      constant := (906371344502805546331003086251427594628714508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75308329551077238303/20000000000000000000)
  centralHi := (94135411938846547879/25000000000000000000)
  directionLo := (379773824186642984509/100000000000000000000)
  directionHi := (37977382418664298451/10000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree060.table
  base := (198027487016458730991585177179790218797/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-815293442283648561719755496822100000000000000)
      constant := (14718925911129304843177499677440400673288898344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree060.table
  base := (198027455532594050566306115158967014509/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-51697318823215014005900691410100000000000000)
      constant := (936843172886601084297714312741089265080403048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379773824186642984509/100000000000000000000)
  centralHi := (37977382418664298451/10000000000000000000)
  directionLo := (95744680851063829787/25000000000000000000)
  directionHi := (382978723404255319149/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree061.table
  base := (4116219393659956695341480384933747616787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1656465433784091387867665186624880000000000000)
      constant := (30411408090946261276877775568549688220411424603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree061.table
  base := (257263687435581516715850579381539779719/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-52517946514656663302700323348040000000000000)
      constant := (967824167535541054196660417815700570987194168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95744680851063829787/25000000000000000000)
  centralHi := (382978723404255319149/100000000000000000000)
  directionLo := (48269628071023958903/12500000000000000000)
  directionHi := (15446280982727666849/4000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree062.table
  base := (5098169880031011099414112332304759220097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1682343983000885652295819379605560000000000000)
      constant := (31400966793429284430466125254867725125167571993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree062.table
  base := (5098169570866964704208977106426867934027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-106677148412196625198999910571960000000000000)
      constant := (1998628656638880303050441262822656951266265643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48269628071023958903/12500000000000000000)
  centralHi := (15446280982727666849/4000000000000000000)
  directionLo := (15572375164572159561/4000000000000000000)
  directionHi := (194654689557151994513/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree063.table
  base := (6114291153615201192283751878577429817251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1708222532217679916723973572586240000000000000)
      constant := (32406527926289064187420255460601234143279450219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree063.table
  base := (3057145455753868027575996700889031308731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-54159201897539961896299587223920000000000000)
      constant := (1031313655135903770837513657247493870160986779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15572375164572159561/4000000000000000000)
  centralHi := (194654689557151994513/50000000000000000000)
  directionLo := (392436412313346321059/100000000000000000000)
  directionHi := (19621820615667316053/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree064.table
  base := (3582291568587072333035760144704070233757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-867050540717237090576063882783460000000000000)
      constant := (16714045743412325778407974837644476632004248533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree064.table
  base := (7164582947626673924077136363142224663353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-109959659177963222386198438323720000000000000)
      constant := (2127644295808021562095860993007621174281346777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392436412313346321059/100000000000000000000)
  centralHi := (19621820615667316053/5000000000000000000)
  directionLo := (79107744943811068293/20000000000000000000)
  directionHi := (197769362359527670733/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree065.table
  base := (8249045769354435286446452402089856101037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1759979630651268445580281958547600000000000000)
      constant := (34465657472890579276044888378156180177997162853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree065.table
  base := (8249045620992730366591094806000767238241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-111600914560846520979797702199600000000000000)
      constant := (2193679613118889979403777473953955694829274369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79107744943811068293/20000000000000000000)
  centralHi := (197769362359527670733/50000000000000000000)
  directionLo := (398616893514791374841/100000000000000000000)
  directionHi := (199308446757395687421/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree066.table
  base := (9367679001108708329571048875750234225017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (83674)
      previous := (0)
      next := (62560)
      square := (2055772601334123809713183554540000000000000)
      linear := (-162350743624369337273494195593480000000000000)
      constant := (3229020534797428186189018004977449994601329043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree066.table
  base := (2341919721252801011438793403550448525647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-56621084971864909786698483037740000000000000)
      constant := (1130366631050742549172739589911205881586308446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398616893514791374841/100000000000000000000)
  centralHi := (199308446757395687421/50000000000000000000)
  directionLo := (200835736883646040913/50000000000000000000)
  directionHi := (401671473767292081827/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree067.table
  base := (1315060349116681939422247339942879736591/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-905868364542428487218295172254480000000000000)
      constant := (18294398357543322845936602103828680246035402716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree067.table
  base := (5260241351052253019662885651509143274137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-57441712663306559083498114975680000000000000)
      constant := (1164402621336399012495864997466613697492568633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200835736883646040913/50000000000000000000)
  centralHi := (401671473767292081827/100000000000000000000)
  directionLo := (25293937474703231127/6250000000000000000)
  directionHi := (404702999595251698033/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree068.table
  base := (11707457112736771994006998253738938193749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (54142)
      previous := (0)
      next := (40480)
      square := (1330205800863256582755589358820000000000000)
      linear := (-108095016370685366992043796322920000000000000)
      constant := (2216139409924303787454831998566820995864541693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree068.table
  base := (5853728520846256258973411607505309963269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-58262340354748208380297746913620000000000000)
      constant := (1198947777382638632901741186229059229708861221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25293937474703231127/6250000000000000000)
  centralHi := (404702999595251698033/100000000000000000000)
  directionLo := (101927996314923268079/25000000000000000000)
  directionHi := (407711985259693072317/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree069.table
  base := (2585720386838394089259824199027833953353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1863493827518445503292898730470320000000000000)
      constant := (38775945642730648203792346760356761627574005285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree069.table
  base := (12928601878634839388572775783600525321763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-118165936092379715354194757703120000000000000)
      constant := (2468004198323387712319198684568513560435774467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101927996314923268079/25000000000000000000)
  centralHi := (407711985259693072317/100000000000000000000)
  directionLo := (410698926182436062737/100000000000000000000)
  directionHi := (205349463091218031369/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree070.table
  base := (14183917235465964899978396097755829858309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1889372376735239767721052923451000000000000000)
      constant := (39893523736375615959689294836686423614315207421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree070.table
  base := (14183917192029002015934105450009929996641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-119807191475263013947794021579000000000000000)
      constant := (2539131173300955775979568553723071935362579969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410698926182436062737/100000000000000000000)
  centralHi := (205349463091218031369/50000000000000000000)
  directionLo := (82732859979674811459/20000000000000000000)
  directionHi := (25854018743648378581/6250000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree071.table
  base := (618936119929469961713237624342492546219/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1915250925952034032149207116431680000000000000)
      constant := (41027104249007365415691180931640555546218305275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree071.table
  base := (3868350741070695896594761491867543502603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-60724223429073156270696642727440000000000000)
      constant := (1305638239829560124921617614141340807194500054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82732859979674811459/20000000000000000000)
  centralHi := (25854018743648378581/6250000000000000000)
  directionLo := (52076070868342723783/12500000000000000000)
  directionHi := (83321713389348358053/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree072.table
  base := (839852960346694881321682706860877169697/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-970564737584414148288680654706180000000000000)
      constant := (21088343590040707185642948823834660137471343930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree072.table
  base := (1049816198774868661987452653683154331587/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-61544851120514805567496274665380000000000000)
      constant := (1342220058682374960611393676161968703347805464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52076070868342723783/12500000000000000000)
  centralHi := (83321713389348358053/20000000000000000000)
  directionLo := (419532171706084682647/100000000000000000000)
  directionHi := (52441521463260585331/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree073.table
  base := (145239086785209093693355725664890765633/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-1967008024385622561005515502393040000000000000)
      constant := (43342272529128958833096460129826605647927547125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree073.table
  base := (9077442913708244776199480765240742650069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-62365478811956454864295906603320000000000000)
      constant := (1379311043194610441472678075389846800514002421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419532171706084682647/100000000000000000000)
  centralHi := (52441521463260585331/12500000000000000000)
  directionLo := (211217771588608048971/50000000000000000000)
  directionHi := (422435543177216097943/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree074.table
  base := (9773441455095842957985189165960288112617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-996443286801208412716834847686860000000000000)
      constant := (22261930147870487043962424045696385315010103873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree074.table
  base := (9773441446996563077600109251128176465117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-63186106503398104161095538541260000000000000)
      constant := (1416911193353735539724786627746062141811443453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211217771588608048971/50000000000000000000)
  centralHi := (422435543177216097943/100000000000000000000)
  directionLo := (212659547859034236199/50000000000000000000)
  directionHi := (425319095718068472399/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree075.table
  base := (20973050382716065345754534622858914157017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2018765122819211089861823888354400000000000000)
      constant := (45721450479555898863372397561444253369156727473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree075.table
  base := (20973050370063549495208602667538190248459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-128013468389679506915790340958400000000000000)
      constant := (2910041018297268562814306013210091862258845931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212659547859034236199/50000000000000000000)
  centralHi := (425319095718068472399/100000000000000000000)
  directionLo := (428183229734002282291/100000000000000000000)
  directionHi := (107045807433500570573/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree076.table
  base := (1402086766029312009701675870125869716297/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1022321836018002677144989040667540000000000000)
      constant := (23467521540125042586802249482829772304873518344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree076.table
  base := (11216694123294003881069228665222067482113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-64827361886281402754694802417140000000000000)
      constant := (1493638990569322260645316704146195547067987617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428183229734002282291/100000000000000000000)
  centralHi := (107045807433500570573/25000000000000000000)
  directionLo := (215514166163414453401/50000000000000000000)
  directionHi := (431028332326828906803/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree077.table
  base := (2990987065383417190435660679896330627457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (41837)
      previous := (0)
      next := (31280)
      square := (1027886300667061904856591777270000000000000)
      linear := (-94114646420581800850824194287080000000000000)
      constant := (2189301731705926517585592394828891740258743212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree077.table
  base := (23927896515352116163152590331510904873221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-131295979155446104102988868710160000000000000)
      constant := (3065533275213453378871178083258767588864945189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215514166163414453401/50000000000000000000)
  centralHi := (431028332326828906803/100000000000000000000)
  directionLo := (108463694476381458167/25000000000000000000)
  directionHi := (433854777905525832669/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree078.table
  base := (3182071896854404671640536806279731152009/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1048200385234796941573143233648220000000000000)
      constant := (24705117765564188106142600191562863674618410884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree078.table
  base := (5091315033762418348377389676409880147679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-132937234538329402696588132586040000000000000)
      constant := (3144806900505030919005331844394507126231114555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108463694476381458167/25000000000000000000)
  centralHi := (433854777905525832669/100000000000000000000)
  directionLo := (436662928761371992009/100000000000000000000)
  directionHi := (43666292876137199201/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree079.table
  base := (13509712102337814674179620347404761132839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1061139659843194073787220330138560000000000000)
      constant := (25335917690397943238145785184911867092054246991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree079.table
  base := (27019424199974231563912458123362240431199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-134578489921212701290187396461920000000000000)
      constant := (3225098856997928051910940868650247189112518591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436662928761371992009/100000000000000000000)
  centralHi := (43666292876137199201/10000000000000000000)
  directionLo := (439453135610004398853/100000000000000000000)
  directionHi := (219726567805002199427/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree080.table
  base := (3577055450746242541151816000302128975213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1074078934451591206001297426628900000000000000)
      constant := (25974718823150734647734858011922260592536893588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree080.table
  base := (14308221801150413651608873993890127145361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-68109872652047999941893330168900000000000000)
      constant := (1653204572338851489947923018116503290864102449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439453135610004398853/100000000000000000000)
  centralHi := (219726567805002199427/50000000000000000000)
  directionLo := (442225738102692074943/100000000000000000000)
  directionHi := (6909777157854563671/1562500000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree081.table
  base := (302476333724995395651806729138337733583/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1087018209059988338215374523119240000000000000)
      constant := (26621521163713832685552535609051196610283196350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree081.table
  base := (967924267828367995953155802484865501/320000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-68930500343489649238692962106840000000000000)
      constant := (1694368881765379235279242104362811685807953125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442225738102692074943/100000000000000000000)
  centralHi := (6909777157854563671/1562500000000000000)
  directionLo := (111245266327234314787/25000000000000000000)
  directionHi := (444981065308937259149/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree082.table
  base := (15956496749192015373311532811441560371157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1099957483668385470429451619609580000000000000)
      constant := (27276324711984421562323011641142579924618989133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree082.table
  base := (31912993496150317089261123584279950376507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-139502256069862597070985188089560000000000000)
      constant := (3472084713544213994700850744575434410381703963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111245266327234314787/25000000000000000000)
  centralHi := (444981065308937259149/100000000000000000000)
  directionLo := (55964929521543133777/12500000000000000000)
  directionHi := (447719436172345070217/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree083.table
  base := (33612523978032580991386732784394620002547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2225793516553565205287057432199840000000000000)
      constant := (55878258935729496721036494953485555466869066043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree083.table
  base := (16806261988145059954017245722868749904259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-70571755726372947832292225982720000000000000)
      constant := (1778224997352902416499188111779447068538508131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55964929521543133777/12500000000000000000)
  centralHi := (447719436172345070217/100000000000000000000)
  directionLo := (450441159941549364973/100000000000000000000)
  directionHi := (225220579970774682487/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree084.table
  base := (35346224806105352145773136049221813662013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2251672065770359469715211625180520000000000000)
      constant := (57219870862522897359879802044172277601946932597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree084.table
  base := (35346224804746301381865650967505654989771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-142784766835629194258183715841320000000000000)
      constant := (3641833607003802063702949473355059991872404139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450441159941549364973/100000000000000000000)
  centralHi := (225220579970774682487/50000000000000000000)
  directionLo := (11328663414446073273/2500000000000000000)
  directionHi := (453146536577842930921/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree085.table
  base := (37114095977482768849689973373570667842529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (54142)
      previous := (0)
      next := (40480)
      square := (1330205800863256582755589358820000000000000)
      linear := (-133973565587479631420197989303600000000000000)
      constant := (3445734423774706977082875108480934863752082153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree085.table
  base := (37114095976422913082826713888481682815451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-144426022218512492851782979717200000000000000)
      constant := (3728235550426948736737277788795156037339331259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11328663414446073273/2500000000000000000)
  centralHi := (453146536577842930921/100000000000000000000)
  directionLo := (91167171428206595719/20000000000000000000)
  directionHi := (113958964285258244649/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree086.table
  base := (3891613748724087388870280095876320932659/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1151714582101973999285760005570940000000000000)
      constant := (29975550980249337306396080644150215333470762855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree086.table
  base := (304032324112612966007662835169592816559/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-73033638800697895722691121796540000000000000)
      constant := (1907827912482204306423421348134056354033845184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91167171428206595719/20000000000000000000)
  centralHi := (113958964285258244649/25000000000000000000)
  directionLo := (3582104719960366527/781250000000000000)
  directionHi := (458509404154926915457/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree087.table
  base := (5094043666328927431894055176130207421429/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1164653856710371131499837102061280000000000000)
      constant := (30670360565671411944721810801096818893279802804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree087.table
  base := (8150469865997423294252494792432891958549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-147708532984279090038981507468960000000000000)
      constant := (3904094430605724673470218364798481291682173705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3582104719960366527/781250000000000000)
  centralHi := (458509404154926915457/100000000000000000000)
  directionLo := (57645931494218435809/12500000000000000000)
  directionHi := (461167451953747486473/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree088.table
  base := (1704909260122626002373965390678251395151/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31790000000000000000000000000000000000000000
      center := (83674)
      previous := (0)
      next := (62560)
      square := (2055772601334123809713183554540000000000000)
      linear := (-214107842057957866129802581554840000000000000)
      constant := (5704212974231091113604026960900314029629625725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree088.table
  base := (21311365751281697013162870052935348640873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-74674894183581194316290385672420000000000000)
      constant := (1996775683670392622125166887131414185147688457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57645931494218435809/12500000000000000000)
  centralHi := (461167451953747486473/100000000000000000000)
  directionLo := (463810267010679574277/100000000000000000000)
  directionHi := (231905133505339787139/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree089.table
  base := (11131821000025242446337542163485792826413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1190532405927165395927991295041960000000000000)
      constant := (32083983357970428278404792741131939378693672394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree089.table
  base := (22263641999854747341182510954920925416367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-75495521875022843613090017610360000000000000)
      constant := (2042013317579898033109265155677890324244754703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463810267010679574277/100000000000000000000)
  centralHi := (231905133505339787139/50000000000000000000)
  directionLo := (29152381765603899153/6250000000000000000)
  directionHi := (466438108249662386449/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree090.table
  base := (23233003408714934712740038680496489126587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1203471680535562528142068391532300000000000000)
      constant := (32802796564694378760728142489448281728267620803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree090.table
  base := (580825085214059739501150003746064760381/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-76316149566464492909889649548300000000000000)
      constant := (2087760117026628513603430039621002282227265160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29152381765603899153/6250000000000000000)
  centralHi := (466438108249662386449/100000000000000000000)
  directionLo := (18762049093658385433/4000000000000000000)
  directionHi := (234525613670729817913/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree091.table
  base := (48438899950870630131666846247692576455181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2432821910287919320712290976045280000000000000)
      constant := (67059221956739474617186164779840901706061224389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree091.table
  base := (4843889995063289192361443388765794903693/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-77136777257906142206689281486240000000000000)
      constant := (2134016082005971278918268558347988204711289185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18762049093658385433/4000000000000000000)
  centralHi := (234525613670729817913/50000000000000000000)
  directionLo := (235824934492482970159/50000000000000000000)
  directionHi := (471649868984965940319/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree092.table
  base := (50445963396359429135283040243370422885397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2458700459504713585140445169025960000000000000)
      constant := (68528853197850900025603092108110580317879447693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree092.table
  base := (2522298169808709831050714412226783590073/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-77957404949347791503488913424180000000000000)
      constant := (2180781212513442460703087242831769649504712570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235824934492482970159/50000000000000000000)
  centralHi := (471649868984965940319/100000000000000000000)
  directionLo := (237117135587319701757/50000000000000000000)
  directionHi := (94846854234927880703/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree093.table
  base := (26243598574971778585808762478471696921907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1242289504360753924784299681003320000000000000)
      constant := (35007243426292405728214691652591906769662165883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree093.table
  base := (52487197149799251235932688734842071428027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-157556065281578881600577090724240000000000000)
      constant := (4456111017089359800501635432074926135784511643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237117135587319701757/50000000000000000000)
  centralHi := (94846854234927880703/20000000000000000000)
  directionLo := (238402332727443811433/50000000000000000000)
  directionHi := (476804665454887622867/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree094.table
  base := (5456260120777552217706836439150029152267/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1255228778969151056998376777493660000000000000)
      constant := (35758061460403332979846471135592306847128123615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree094.table
  base := (54562601207663113198145632686929736724031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (1242)
      previous := (0)
      next := (920)
      square := (30393618201542566548134516220000000000000)
      linear := (-3387177035414088940301624565960000000000000)
      constant := (96844211493422845042240322000605697626029457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238402332727443811433/50000000000000000000)
  centralHi := (476804665454887622867/100000000000000000000)
  directionLo := (29960079822636043909/6250000000000000000)
  directionHi := (95872255432435340509/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree095.table
  base := (28336087783053931992232078983266929343421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1268168053577548189212453873984000000000000000)
      constant := (36516880701192709300403976149606611252210088949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree095.table
  base := (11334435113204062290597275954219705497289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-160838576047345478787775618476000000000000000)
      constant := (4648263194323152925297394762135856647217557005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29960079822636043909/6250000000000000000)
  centralHi := (95872255432435340509/20000000000000000000)
  directionLo := (120476081413894941977/25000000000000000000)
  directionHi := (481904325655579767909/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree096.table
  base := (58815920221288543500778893845714962756417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2562214656371890642853061940948680000000000000)
      constant := (74567402297193361224730386781365046532629146073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree096.table
  base := (7351990027652544822523301101088453691501/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-81239915715114388690687441175940000000000000)
      constant := (2372933389739066749363280576556737576818102836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120476081413894941977/25000000000000000000)
  centralHi := (481904325655579767909/100000000000000000000)
  directionLo := (242217012268216289259/50000000000000000000)
  directionHi := (484434024536432578519/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree097.table
  base := (30496917584878399907853969828677240341311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1294046602794342453640608066964680000000000000)
      constant := (38058522802552988791593901514117244417495304359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree097.table
  base := (60993835169703703926998528352281197079081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-164121086813112075974974146227760000000000000)
      constant := (4844488695647952389880875761053849164347689929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242217012268216289259/50000000000000000000)
  centralHi := (484434024536432578519/100000000000000000000)
  directionLo := (6086882273221484343/1250000000000000000)
  directionHi := (486950581857718747441/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree098.table
  base := (12641184081607878373458633940347207640699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2613971754805479171709370326910040000000000000)
      constant := (77682691326001811909484587342228167519938016655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree098.table
  base := (15801480101999512565404500242130098687881/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-82881171097997687284286705051820000000000000)
      constant := (2472064471412469647087640960483410776003058258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6086882273221484343/1250000000000000000)
  centralHi := (486950581857718747441/100000000000000000000)
  directionLo := (489454200323765463089/100000000000000000000)
  directionHi := (48945420032376546309/10000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree099.table
  base := (3272608796637357961543653795400756406351/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (41837)
      previous := (0)
      next := (31280)
      square := (1027886300667061904856591777270000000000000)
      linear := (-119993195637376065278978387267760000000000000)
      constant := (3602924520898288575124125065800760046157898290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree099.table
  base := (65452175932714973111762630955065399826581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-167403597578878673162172673979520000000000000)
      constant := (5044787521001609181950508262545879468216917429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489454200323765463089/100000000000000000000)
  centralHi := (48945420032376546309/10000000000000000000)
  directionLo := (245972538740396087619/50000000000000000000)
  directionHi := (491945077480792175239/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree100.table
  base := (33866300870285925247367123774069400973599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1332864426619533850282839356435700000000000000)
      constant := (40430995003135950784655044542325432882645783431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree100.table
  base := (33866300870273397423776455435771192151571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-84522426480880985877885968927700000000000000)
      constant := (2573232215085327696661075476927618563462820339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245972538740396087619/50000000000000000000)
  centralHi := (491945077480792175239/100000000000000000000)
  directionLo := (494423405898819176831/100000000000000000000)
  directionHi := (3862682858584524819/781250000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree101.table
  base := (70047197828283178461434201771816239461187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2691607402455861964993832905852080000000000000)
      constant := (82475642965417510746215234070538782077718248203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree101.table
  base := (35023598914131837779355464482236014423621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-85343054172322635174685600865640000000000000)
      constant := (2624579835162471605964203043915729355861778789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494423405898819176831/100000000000000000000)
  centralHi := (3862682858584524819/781250000000000000)
  directionLo := (248444686672705070853/50000000000000000000)
  directionHi := (496889373345410141707/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree102.table
  base := (9049495524090758722335574691739782808741/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10285000000000000000000000000000000000000000
      center := (27071)
      previous := (0)
      next := (20240)
      square := (665102900431628291377794679410000000000000)
      linear := (-79926057402136947924176091142140000000000000)
      constant := (2473685245208495483040882806096274932950320948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree102.table
  base := (72395964192710890527108858836914072445223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-172327363727528568942970465607160000000000000)
      constant := (5352873241457503850866929295963703186031497607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248444686672705070853/50000000000000000000)
  centralHi := (496889373345410141707/100000000000000000000)
  directionLo := (31208947684480765123/6250000000000000000)
  directionHi := (499343162951692241969/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree103.table
  base := (74778900830818083106298795926195068353679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2743364500889450493850141291813440000000000000)
      constant := (85750956121178118709609446518871975345259800951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree103.table
  base := (18694725207701567529535370729731240956711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-86984309555205933768284864741520000000000000)
      constant := (2728802571780764398707438826319982622546749198) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31208947684480765123/6250000000000000000)
  centralHi := (499343162951692241969/100000000000000000000)
  directionLo := (250892476685534632549/50000000000000000000)
  directionHi := (501784953371069265099/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree104.table
  base := (77196007739546974989101377281010991362731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2769243050106244758278295484794120000000000000)
      constant := (87412616317579992463489498154977113356963340339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree104.table
  base := (7719600773953778260230264376946659582001/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-87804937246647583065084496679460000000000000)
      constant := (2781677688315182236740886028036495855083201045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250892476685534632549/50000000000000000000)
  centralHi := (501784953371069265099/100000000000000000000)
  directionLo := (504214918931016996189/100000000000000000000)
  directionHi := (50421491893101699619/10000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree105.table
  base := (79647284915968396556325622176327535407363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2795121599323039022706449677774800000000000000)
      constant := (89090278926191506749368328904119497585660076747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree105.table
  base := (79647284915961244075408068080142593061857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-177251129876178464723768257234800000000000000)
      constant := (5670123940657507176823269446524534988073642113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504214918931016996189/100000000000000000000)
  centralHi := (50421491893101699619/10000000000000000000)
  directionLo := (101326645955665171551/20000000000000000000)
  directionHi := (126658307444581464439/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree106.table
  base := (41066366178601853628906929307102174401057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1410500074269916643567301935377740000000000000)
      constant := (45391971973455999192923737567101575936630562233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree106.table
  base := (16426546471439628501245123276947599731241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-178892385259061763317367521110680000000000000)
      constant := (5777910835636598274362378027913726239031556845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101326645955665171551/20000000000000000000)
  centralHi := (126658307444581464439/25000000000000000000)
  directionLo := (101808010403626651303/20000000000000000000)
  directionHi := (127260013004533314129/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree107.table
  base := (84652350060437894270734835229022768110031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2846878697756627551562758063736160000000000000)
      constant := (92493611379643029189525350816223757178039674039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree107.table
  base := (2645385939388548912010616025983145653199/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-90266820320972530955483392493280000000000000)
      constant := (2943358030780709811960894896591978299966665456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101808010403626651303/20000000000000000000)
  centralHi := (127260013004533314129/25000000000000000000)
  directionLo := (51143554784706713491/10000000000000000000)
  directionHi := (511435547847067134911/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree108.table
  base := (87206138022917588117649298377578423052071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2872757246973421815990912256716840000000000000)
      constant := (94219281224288316583145382689532099875707870799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree108.table
  base := (21801534505728555152017377611545538966189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-91087448012414180252283024431220000000000000)
      constant := (2998269809212944602287145875684688191152623002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51143554784706713491/10000000000000000000)
  centralHi := (511435547847067134911/100000000000000000000)
  directionLo := (513819875680802738749/100000000000000000000)
  directionHi := (411055900544642191/80000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree109.table
  base := (44897048120974583271749340073087667459611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1449317898095108040209533224848760000000000000)
      constant := (47980476740376833645035213846377072643395137059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree109.table
  base := (89794096241946547249536969322469248548079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-183816151407711659098165312738320000000000000)
      constant := (6107381506224056938904801312316674570042706511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513819875680802738749/100000000000000000000)
  centralHi := (411055900544642191/80000000000000000)
  directionLo := (412954552221053181/80000000000000000)
  directionHi := (516193190276316476251/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree110.table
  base := (2310405617872423497374685114464113158313/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (41837)
      previous := (0)
      next := (31280)
      square := (1027886300667061904856591777270000000000000)
      linear := (-132932470245773197493055483758100000000000000)
      constant := (4441755824952132449037017855921628314605540540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree110.table
  base := (92416224714894902744374862993224926995469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-185457406790594957691764576614200000000000000)
      constant := (6219241724950100692930431272760033863732991021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412954552221053181/80000000000000000)
  centralHi := (516193190276316476251/100000000000000000000)
  directionLo := (103711128569820770559/20000000000000000000)
  directionHi := (129638910712275963199/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree111.table
  base := (47536261719590706100023430374868738037899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1475196447311902304637687417829440000000000000)
      constant := (49746152614388926977365005423330254900447290131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree111.table
  base := (47536261719589913970505505162654370694829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-93549331086739128142681920245040000000000000)
      constant := (3166060137299161220692679342288173504864877261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103711128569820770559/20000000000000000000)
  centralHi := (129638910712275963199/25000000000000000000)
  directionLo := (130226845296403180963/25000000000000000000)
  directionHi := (520907381185612723853/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree112.table
  base := (19552598482455522582214214729898797182133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-2976271443840598873703529028639560000000000000)
      constant := (101281984720158191822738048401776515193310044385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree112.table
  base := (97762992412276380958332039976422331214851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-188739917556361554878963104365960000000000000)
      constant := (6446017155163144587654204110470476929653605859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130226845296403180963/25000000000000000000)
  centralHi := (520907381185612723853/100000000000000000000)
  directionLo := (523248549751128428079/100000000000000000000)
  directionHi := (6540606871889105351/1250000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree113.table
  base := (25121907907928373723687198752021742639421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1501074996528696569065841610810120000000000000)
      constant := (51543833311500741233316872227439526636715825898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree113.table
  base := (100487631631712536978964560087971693070813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-190381172939244853472562368241840000000000000)
      constant := (6560932366639106428915389727826789469993425917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523248549751128428079/100000000000000000000)
  centralHi := (6540606871889105351/1250000000000000000)
  directionLo := (262789644896666831539/50000000000000000000)
  directionHi := (525579289793333663079/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree114.table
  base := (103246441095068394755572441846203832447313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-3028028542274187402559837414600920000000000000)
      constant := (104909350937223077708139594336764541816850088297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree114.table
  base := (103246441095067649977899213005485884353927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-192022428322128152066161632117720000000000000)
      constant := (6676865909020860758099669865586558318537824743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262789644896666831539/50000000000000000000)
  centralHi := (525579289793333663079/100000000000000000000)
  directionLo := (527899739441753174091/100000000000000000000)
  directionHi := (131974934860438293523/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree115.table
  base := (106039420799971551994254844725205380826147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-3053907091490981666987991607581600000000000000)
      constant := (106747037662740074423356025019333206962109534443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree115.table
  base := (106039420799970972975541298382383947437663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-193663683705011450659760895993600000000000000)
      constant := (6793817782303170595129119830684186139889797567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527899739441753174091/100000000000000000000)
  centralHi := (131974934860438293523/25000000000000000000)
  directionLo := (530210033803281373569/100000000000000000000)
  directionHi := (53021003380328137357/10000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree116.table
  base := (3402080335753146370172693537478366266963/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1539892820353887965708072900281140000000000000)
      constant := (54300363399735632353132158250553215839830866352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree116.table
  base := (3402080335753132304005242362290482129823/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-97652469543947374626680079934740000000000000)
      constant := (3455893993240453020308677691099114800396464112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530210033803281373569/100000000000000000000)
  centralHi := (53021003380328137357/10000000000000000000)
  directionLo := (532510305053979835033/100000000000000000000)
  directionHi := (266255152526989917517/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree117.table
  base := (2234557818503612258540148461381353573917/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1552832094962285097922149996771480000000000000)
      constant := (55235209173668543939490027643046943828157589325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree117.table
  base := (22345578185036052608180280333241202824593/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-196946194470778047846959423745360000000000000)
      constant := (7030776521549041245812892822943509085197629685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532510305053979835033/100000000000000000000)
  centralHi := (266255152526989917517/50000000000000000000)
  directionLo := (534800682527321151187/100000000000000000000)
  directionHi := (133700170631830287797/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree118.table
  base := (22924676268196389014726129331509188329383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-3131542739141364460272454186523640000000000000)
      constant := (112356112306259584256944982410120684033450970635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree118.table
  base := (114623381340981673119314420454405542950357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-198587449853661346440558687621240000000000000)
      constant := (7150783387502651493077841107051941844377338613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534800682527321151187/100000000000000000000)
  centralHi := (133700170631830287797/25000000000000000000)
  directionLo := (268540646399522930707/50000000000000000000)
  directionHi := (107416258559809172283/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree119.table
  base := (23510608397863958987879055720091311400199/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20570000000000000000000000000000000000000000
      center := (54142)
      previous := (0)
      next := (40480)
      square := (1330205800863256582755589358820000000000000)
      linear := (-185730664021068160276506375264960000000000000)
      constant := (6721047569186020622617341376681359137751046715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree119.table
  base := (29388260497329895893477156856710169125833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-100114352618272322517078975748560000000000000)
      constant := (3635904292168455190815899372447215527197930194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268540646399522930707/50000000000000000000)
  centralHi := (107416258559809172283/20000000000000000000)
  directionLo := (539352259768789989711/100000000000000000000)
  directionHi := (33709516235549374357/6250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree120.table
  base := (19282699658888409140339773438285306591/1600000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1591649918787476494564381286242500000000000000)
      constant := (58087753728485248531247805027232621519314621875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree120.table
  base := (120516872868052392863434234496815366642297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-201869960619427943627757215373000000000000000)
      constant := (7393852112047087113670144954587465144912834073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539352259768789989711/100000000000000000000)
  centralHi := (33709516235549374357/6250000000000000000)
  directionLo := (541613704738632146349/100000000000000000000)
  directionHi := (10832274094772642927/2000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree121.table
  base := (6175743698754036038138978703609202536209/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15895000000000000000000000000000000000000000
      center := (41837)
      previous := (0)
      next := (31280)
      square := (1027886300667061904856591777270000000000000)
      linear := (-145871744854170329707132580248440000000000000)
      constant := (5368600393118663904326965357822906548626084110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree121.table
  base := (123514873975080593113325490432152029940933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-203511216002311242221356479248880000000000000)
      constant := (7516913970628543876297963991659163834139520997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541613704738632146349/100000000000000000000)
  centralHi := (10832274094772642927/2000000000000000000)
  directionLo := (271932873244350547257/50000000000000000000)
  directionHi := (108773149297740218903/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree122.table
  base := (31636761327086431392031722367973995844629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1617528468004270758992535479223180000000000000)
      constant := (60029456125505345644109019802717845321381663002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree122.table
  base := (126547045308345626378390215409986274493027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-205152471385194540814955743124760000000000000)
      constant := (7640994160076733315014326330880819680355096643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271932873244350547257/50000000000000000000)
  centralHi := (108773149297740218903/20000000000000000000)
  directionLo := (136527125337494282297/25000000000000000000)
  directionHi := (546108501349977129189/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree123.table
  base := (32403346716457214401845645504801976131217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1630467742612667891206612575713520000000000000)
      constant := (61012309132050080416974810669965670606665054546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree123.table
  base := (129613386865828780537378203657896510843423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-206793726768077839408555007000640000000000000)
      constant := (7766092680387196094743390267701153392453121407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136527125337494282297/25000000000000000000)
  centralHi := (546108501349977129189/100000000000000000000)
  directionLo := (548342083274413525063/100000000000000000000)
  directionHi := (68542760409301690633/12500000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree124.table
  base := (132713898645550182992723988829355216557787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-3286814034442130046841379344407720000000000000)
      constant := (124006326687809778224264712377173562567809253603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree124.table
  base := (66356949322775061556804463141786374346673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-104217491075480569001077135438260000000000000)
      constant := (3946104765777779272322084256898526100931800657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (548342083274413525063/100000000000000000000)
  centralHi := (68542760409301690633/12500000000000000000)
  directionLo := (550566603902497651269/100000000000000000000)
  directionHi := (55056660390249765127/10000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree125.table
  base := (27169716129113503586423027266845045257763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-3312692583658924311269533537388400000000000000)
      constant := (126004037522071627234139606757459021938093571735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree125.table
  base := (135848580645567471412387035973089027486057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-210076237533844436595753534752400000000000000)
      constant := (8019344713577530383144079046952053661716699913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550566603902497651269/100000000000000000000)
  centralHi := (55056660390249765127/10000000000000000000)
  directionLo := (276391086314182546839/50000000000000000000)
  directionHi := (552782172628365093679/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree126.table
  base := (27803486572795086718519972709504740425067/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-3338571132875718575697687730369080000000000000)
      constant := (128017750766819076922714660487257996339620839615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree126.table
  base := (139017432863975397454008802120654482883901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-211717492916727735189352798628280000000000000)
      constant := (8147498226448902519835956326257965752690537309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276391086314182546839/50000000000000000000)
  centralHi := (552782172628365093679/100000000000000000000)
  directionLo := (34686806041410890203/6250000000000000000)
  directionHi := (554988896662574243249/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree127.table
  base := (71110227649452147167143622190795792942387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 174845000000000000000000000000000000000000000
      center := (460207)
      previous := (0)
      next := (344080)
      square := (11306749307337680953422509549970000000000000)
      linear := (-1682224841046256420062920961674880000000000000)
      constant := (65023733210993374000649263886105568083402331003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree127.table
  base := (142220455298904266261989608936334270050953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (58374)
      previous := (0)
      next := (43240)
      square := (1428500055472500627762322262340000000000000)
      linear := (-213358748299611033782952062504160000000000000)
      constant := (8276670070165544931056745835434822402542555177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34686806041410890203/6250000000000000000)
  centralHi := (554988896662574243249/100000000000000000000)
  directionLo := (557186881092643276003/100000000000000000000)
  directionHi := (139296720273160819001/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree128.table
  base := (5818305917940773117831762975817947438969/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-3390328231309307104553996116330440000000000000)
      constant := (132093184487510480320431349336221805099832674025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree128.table
  base := (72728823974259653070353475725480776373223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-107500001841247166188275663190020000000000000)
      constant := (4203430122361702303065408730502867035008449607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell168.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557186881092643276003/100000000000000000000)
  centralHi := (139296720273160819001/25000000000000000000)
  directionLo := (55937622894144624353/10000000000000000000)
  directionHi := (559376228941446243531/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 187
  table := BinomialMassData.Q107_187.Degree129.table
  base := (148729010811019726581770650711037677261237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 349690000000000000000000000000000000000000000
      center := (920414)
      previous := (0)
      next := (688160)
      square := (22613498614675361906845019099940000000000000)
      linear := (-3416206780526101368982150309311120000000000000)
      constant := (134154904963327301430569091419347216536148196653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_187.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 27
  qDenominator := 47
  table := BinomialMassData.Q27_47.Degree129.table
  base := (74364505405509854822877719929718559799603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11045000000000000000000000000000000000000000
      center := (29187)
      previous := (0)
      next := (21620)
      square := (714250027736250313881161131170000000000000)
      linear := (-108320629532688815485075295127960000000000000)
      constant := (4269034375059251780706739848445618298597323027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_47.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell168.Kernel129
