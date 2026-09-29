import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell164.Parameters
import ForestUnimodality.BinomialMassData.Q116_207.Batch000_049
import ForestUnimodality.BinomialMassData.Q116_207.Batch050_099
import ForestUnimodality.BinomialMassData.Q116_207.Batch100_149
import ForestUnimodality.BinomialMassData.Q13_23.Batch000_049
import ForestUnimodality.BinomialMassData.Q13_23.Batch050_099
import ForestUnimodality.BinomialMassData.Q13_23.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree000.table
  base := (238356098816658753991504229/10000000000000000000000000)
  polynomial :=
    { denominator := 414000000000000000000000000000000000000000
      center := (1276)
      previous := (0)
      next := (1001)
      square := (29940209480820207166296143148000000000000)
      linear := (-112121439510060827760007383480000000000000)
      constant := (9867942491009672415248275080600000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree000.table
  base := (238356098816658753991504229/10000000000000000000000000)
  polynomial :=
    { denominator := 46000000000000000000000000000000000000000
      center := (143)
      previous := (0)
      next := (110)
      square := (3326689942313356351810682572000000000000)
      linear := (-12457937723340091973334153720000000000000)
      constant := (1096438054556630268360919453400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree001.table
  base := (28354320686931332470021707571309267100749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-30155266578132879408902233590696000000000000)
      constant := (1229906632352434178552902071367094785999993901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree001.table
  base := (140933350767129132537582508796401407967513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-1865132530684846902668816412160000000000000)
      constant := (75485728203535146921833955265676344814814377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49572844569527738223/100000000000000000000)
  directionHi := (3098302785595483639/6250000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree002.table
  base := (3524544732924913241165598627002839128101/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-37101395177683167471482938801032000000000000)
      constant := (788913293291617979492969659451119268999998745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree002.table
  base := (87180508723342424204047690845340471072837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-2297602223185583228404205146520000000000000)
      constant := (48226899801509273685219020923105109197530773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49572844569527738223/100000000000000000000)
  centralHi := (3098302785595483639/6250000000000000000)
  directionLo := (35053294557819781097/50000000000000000000)
  directionHi := (14021317823127912439/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree003.table
  base := (57439833389550675572478781950867541258781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-24470846542907475296702024450760000000000000)
      constant := (304879149680994814058078244142800363933056341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree003.table
  base := (28317301916811660133510603203224286748347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-2730071915686319554139593880880000000000000)
      constant := (33488980545398622836729171249631295379751126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35053294557819781097/50000000000000000000)
  centralHi := (14021317823127912439/20000000000000000000)
  directionLo := (85862685470136952249/100000000000000000000)
  directionHi := (343450741880547809/400000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree004.table
  base := (39205264144019764204254178294591635330247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-254968261883918717983221746108520000000000000)
      constant := (2095728763366160598773789788249276982265753703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree004.table
  base := (3855901352024147467454986780890802033593/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-632508321637411175974996523048000000000000)
      constant := (5118459418316768262976233993478468551541394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85862685470136952249/100000000000000000000)
  centralHi := (343450741880547809/400000000000000000)
  directionLo := (49572844569527738223/50000000000000000000)
  directionHi := (99145689139055476447/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree005.table
  base := (2781185919260444778330521822551861492431/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-57939780976334031659225054432040000000000000)
      constant := (352028962198278314833700020577049426178351838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree005.table
  base := (27297055038595094116150029293406509508431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-3595011300687792205610371349600000000000000)
      constant := (21544464268170580458429168469712043529959999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49572844569527738223/50000000000000000000)
  centralHi := (99145689139055476447/100000000000000000000)
  directionLo := (110848250295495322391/100000000000000000000)
  directionHi := (13856031286936915299/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree006.table
  base := (20274629210663619065243005200315260502687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-36047727542157955401003199801320000000000000)
      constant := (178806298048122160932446145911980955253292807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree006.table
  base := (19854453171727451011807919409380923884539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-4027480993188528531345760083960000000000000)
      constant := (19761510485388731377545881659242508734921131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110848250295495322391/100000000000000000000)
  centralHi := (13856031286936915299/12500000000000000000)
  directionLo := (60714087146821483347/50000000000000000000)
  directionHi := (24285634858728593339/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree007.table
  base := (3745793874256666485730859608234739119667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-359160190877173038921932324263560000000000000)
      constant := (1574060403744824663265317844635881346154445132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree007.table
  base := (3656723362828111390023516821091572539893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-4459950685689264857081148818320000000000000)
      constant := (19394753389493787277275119444449767494413588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60714087146821483347/50000000000000000000)
  centralHi := (24285634858728593339/20000000000000000000)
  directionLo := (65578709256514591679/50000000000000000000)
  directionHi := (131157418513029183359/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree008.table
  base := (11055904698069514366670137108409191622973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-393890833874924479234835850315240000000000000)
      constant := (1616780581317129269833824455628305451852770077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree008.table
  base := (5370766915544443032751650245979255799143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-4892420378190001182816537552680000000000000)
      constant := (19982459538013577750694645611766052635493294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65578709256514591679/50000000000000000000)
  centralHi := (131157418513029183359/100000000000000000000)
  directionLo := (35053294557819781097/25000000000000000000)
  directionHi := (140213178231279124389/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree009.table
  base := (8000002071545332280220379333790213580819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-47624608541408435505304375151880000000000000)
      constant := (190700066251053195702081530643855206858279259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree009.table
  base := (7712953709219587022604005633939058446929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-5324890070690737508551926287040000000000000)
      constant := (21267841432576231665431136673533761918425441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35053294557819781097/25000000000000000000)
  centralHi := (140213178231279124389/100000000000000000000)
  directionLo := (148718533708583214669/100000000000000000000)
  directionHi := (14871853370858321467/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree010.table
  base := (345749000407216677930500433347198202761/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-463352119870427359860642902418600000000000000)
      constant := (1860473459326762802320880613471905532641697424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree010.table
  base := (5262952547421010845040861754678697818729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-5757359763191473834287315021400000000000000)
      constant := (23103730988429757638302627844225031146107641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148718533708583214669/100000000000000000000)
  centralHi := (14871853370858321467/10000000000000000000)
  directionLo := (156763098933216925787/100000000000000000000)
  directionHi := (39190774733304231447/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree011.table
  base := (1741314601557508500102691777079052973499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-498082762868178800173546428470280000000000000)
      constant := (2042048207041070247043193218546840681722917302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree011.table
  base := (806445155765039419491642172954912186533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-6189829455692210160022703755760000000000000)
      constant := (25402446602301298746094897337952594186703828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156763098933216925787/100000000000000000000)
  centralHi := (39190774733304231447/25000000000000000000)
  directionLo := (20551815653466344583/12500000000000000000)
  directionHi := (32882905045546151333/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree012.table
  base := (34926281790286507084692761593550290189/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (29348)
      previous := (0)
      next := (23023)
      square := (688624818058864764824811292404000000000000)
      linear := (-11840297908131783121921110100488000000000000)
      constant := (50144421666068269025680438923852929315898290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree012.table
  base := (748992778107410733316750951277346651761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-6622299148192946485758092490120000000000000)
      constant := (28109261965212007985846451771571432757563138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20551815653466344583/12500000000000000000)
  centralHi := (32882905045546151333/20000000000000000000)
  directionLo := (171725370940273904499/100000000000000000000)
  directionHi := (343450741880547809/200000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree013.table
  base := (63443223457845141125710555466276094569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-567544048863681680799353480573640000000000000)
      constant := (2500857794063396075558839708328377857504748324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree013.table
  base := (11619283336586705227447610721410253283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-7054768840693682811493481224480000000000000)
      constant := (31188232551544773554981572057491626023986707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171725370940273904499/100000000000000000000)
  centralHi := (343450741880547809/200000000000000000)
  directionLo := (2792772390094356747/1562500000000000000)
  directionHi := (178737432966038831809/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree014.table
  base := (-41709548783886518078814783625431652683/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-120454938372286624222451401325064000000000000)
      constant := (554615773454640692073545480888953395570930665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree014.table
  base := (-160034330358626816217861854385509532451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-7487238533194419137228869958840000000000000)
      constant := (34614518400680821921973360151120523658667368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2792772390094356747/1562500000000000000)
  centralHi := (178737432966038831809/100000000000000000000)
  directionLo := (46371150016742482067/25000000000000000000)
  directionHi := (185484600066969928269/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree015.table
  base := (-544418752902882164000211344375089506301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-70778370539909395713906725853000000000000000)
      constant := (341298429331083502834420507569720795442003756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree015.table
  base := (-2411678875722940886574896666190090511837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-7919708225695155462964258693200000000000000)
      constant := (38370142689013365961872506671085442119238227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46371150016742482067/25000000000000000000)
  centralHi := (185484600066969928269/100000000000000000000)
  directionLo := (95997400720954857117/50000000000000000000)
  directionHi := (38398960288381942847/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree016.table
  base := (-99277643351002921370413179159662555863/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-671735977856936001738064058728680000000000000)
      constant := (3395571197306522139643007785943923812602442016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree016.table
  base := (-3408153786230485540054996613643111767267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-8352177918195891788699647427560000000000000)
      constant := (42441583980280605585216985528662793875115757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95997400720954857117/50000000000000000000)
  centralHi := (38398960288381942847/20000000000000000000)
  directionLo := (198291378278110952893/100000000000000000000)
  directionHi := (99145689139055476447/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree017.table
  base := (-812073291919285677103443959272366842551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-141293324170937488410193516956072000000000000)
      constant := (748775585907916705026257499362674353163532201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree017.table
  base := (-4289514239025807189276057634891847742427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-8784647610696628114435036161920000000000000)
      constant := (46818360211091070840186672219362212544256117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198291378278110952893/100000000000000000000)
  centralHi := (99145689139055476447/50000000000000000000)
  directionLo := (40878814864497942299/20000000000000000000)
  directionHi := (25549259290311213937/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree018.table
  base := (-484395910821605252924119117655529024797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (29348)
      previous := (0)
      next := (23023)
      square := (688624818058864764824811292404000000000000)
      linear := (-16471050307831975163641580240712000000000000)
      constant := (91465053281563257714096668502868052625882966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree018.table
  base := (-5071472967088991839882888608245797966721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-9217117303197364440170424896280000000000000)
      constant := (51492159345698296229795462846557972875604591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40878814864497942299/20000000000000000000)
  centralHi := (25549259290311213937/12500000000000000000)
  directionLo := (210319767346918686583/100000000000000000000)
  directionHi := (26289970918364835823/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree019.table
  base := (-5540424616319083214264281963278430822649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-775927906850190322676774636883720000000000000)
      constant := (4511172759194569757497097372598202517680312999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree019.table
  base := (-5766699205132214127900347912262885122359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-9649586995698100765905813630640000000000000)
      constant := (56456279358939541371586207327992933770272089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210319767346918686583/100000000000000000000)
  centralHi := (26289970918364835823/12500000000000000000)
  directionLo := (108041509911210237059/50000000000000000000)
  directionHi := (216083019822420474119/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree020.table
  base := (-30800893600519746924997899764232447491/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-162131709969588352597935632587080000000000000)
      constant := (985833542046377304876074593547296154298325640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree020.table
  base := (-6385534934056634179928681129768289891211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-10082056688198837091641202365000000000000000)
      constant := (61705249342918092558587375750352574647549381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108041509911210237059/50000000000000000000)
  centralHi := (216083019822420474119/100000000000000000000)
  directionLo := (221696500590990644783/100000000000000000000)
  directionHi := (13856031286936915299/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree021.table
  base := (-419487827729151223088880396826171663949/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-93932132538410355922509076554120000000000000)
      constant := (596616049167068590236552893495049547327020976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree021.table
  base := (-277460082996195988537019879916464576203/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-2102905276139914683475318219872000000000000)
      constant := (13446912240280477829652778618336951195943065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221696500590990644783/100000000000000000000)
  centralHi := (13856031286936915299/6250000000000000000)
  directionLo := (2839641408176767679/1250000000000000000)
  directionHi := (227171312654141414321/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree022.table
  base := (-3601216583837517943870746423933411182127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-880119835843444643615485215038760000000000000)
      constant := (5831997486317095759434041514295834528514080354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree022.table
  base := (-232083621071588965650568783941482612351/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-10946996073200309743111979833720000000000000)
      constant := (73040472128933711805401661805758582338122272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2839641408176767679/1250000000000000000)
  centralHi := (227171312654141414321/100000000000000000000)
  directionLo := (7266164107130944371/3125000000000000000)
  directionHi := (232517251428190219873/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree023.table
  base := (-477376370645670095991724001298743595869/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18630000000000000000000000000000000000000000
      center := (57420)
      previous := (0)
      next := (45045)
      square := (1347309426636909322483326441660000000000000)
      linear := (-39776107775704177562103858308280000000000000)
      constant := (274620499378471761229305696831847050894336848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree023.table
  base := (-1572393674696145887700770115196282506611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46000000000000000000000000000000000000000
      center := (143)
      previous := (0)
      next := (110)
      square := (3326689942313356351810682572000000000000)
      linear := (-98951876223487357120411900592000000000000)
      constant := (687998736136367063692231640378485502347947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7266164107130944371/3125000000000000000)
  centralHi := (232517251428190219873/100000000000000000000)
  directionLo := (237743010686822889423/100000000000000000000)
  directionHi := (14858938167926430589/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree024.table
  base := (-8023582570054828492570454992164414682833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-105509013537660836026810251904680000000000000)
      constant := (758016858075729449745624974887585221695032087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree024.table
  base := (-2061837158052243047696801559001533807331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-11811935458201782394582757302440000000000000)
      constant := (85470080149048379952661605158432754463687604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237743010686822889423/100000000000000000000)
  centralHi := (14858938167926430589/6250000000000000000)
  directionLo := (242856348587285933389/100000000000000000000)
  directionHi := (24285634858728593339/10000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree025.table
  base := (-32669344464412034900217376228439428129/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-984311764836698964554195793193800000000000000)
      constant := (7349456641918930398900451862032825329689722624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree025.table
  base := (-2146754170743118644842634799971878040131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-12244405150702518720318146036800000000000000)
      constant := (92088926791841354895486059920759506067082804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242856348587285933389/100000000000000000000)
  centralHi := (24285634858728593339/10000000000000000000)
  directionLo := (61966055711909672779/25000000000000000000)
  directionHi := (247864222847638691117/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree026.table
  base := (-8660933283549456041333422973985383627323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1019042407834450404867099319245480000000000000)
      constant := (7898031879263933074465822503964020296952836773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree026.table
  base := (-1776908510782521167305930173524511127291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-2535374968640651009210706954232000000000000)
      constant := (19794901207834870565841220797981533613663061) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61966055711909672779/25000000000000000000)
  centralHi := (247864222847638691117/100000000000000000000)
  directionLo := (252772901804324052637/100000000000000000000)
  directionHi := (126386450902162026319/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree027.table
  base := (-2229851528530541046689398238080176132041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-117085894536911316131111427255240000000000000)
      constant := (940860605491485514145592147164721125741411196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree027.table
  base := (-4571489143448514151299522073694846257081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-13109344535703991371788923505520000000000000)
      constant := (106125203360899380375784785327450852660008302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252772901804324052637/100000000000000000000)
  centralHi := (126386450902162026319/50000000000000000000)
  directionLo := (257588056410410856749/100000000000000000000)
  directionHi := (1030352225641643427/400000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree028.table
  base := (-4570709857161316924536014361434947039721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1088503693829953285492906371348840000000000000)
      constant := (9058483843694490802165415817674227908589989742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree028.table
  base := (-146327323700406128493134830563769983801/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-13541814228204727697524312239880000000000000)
      constant := (113539630219354205155097673481553003428433344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257588056410410856749/100000000000000000000)
  centralHi := (1030352225641643427/400000000000000000)
  directionLo := (262314837026058366717/100000000000000000000)
  directionHi := (131157418513029183359/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree029.table
  base := (-1865853219562640198983626114312456055291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-224646867365540945161161979480104000000000000)
      constant := (1934029770316775833039292924537489570486835941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree029.table
  base := (-4776362671509267609827840398804949017601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-13974283920705464023259700974240000000000000)
      constant := (121216584991399056266037134028044363939378142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262314837026058366717/100000000000000000000)
  centralHi := (131157418513029183359/50000000000000000000)
  directionLo := (10678317518614783517/4000000000000000000)
  directionHi := (133478968982684793963/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree030.table
  base := (-9484940865988109840855384732286695095347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-128662775536161796235412602605800000000000000)
      constant := (1144739440396376971774235368209583044651052933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree030.table
  base := (-4854143312888150395480122614295045165999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-14406753613206200348995089708600000000000000)
      constant := (129155021071534364297062938550075842214373058) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10678317518614783517/4000000000000000000)
  centralHi := (133478968982684793963/50000000000000000000)
  directionLo := (135760826052139091431/50000000000000000000)
  directionHi := (271521652104278182863/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree031.table
  base := (-1922038572607443794773539133942385709861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-238539124564641521286323389900776000000000000)
      constant := (2191185448684068058777340713772806714718166011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree031.table
  base := (-4916683659643710644771811474169901107059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-14839223305706936674730478442960000000000000)
      constant := (137354020774794607233930427083508244628731578) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135760826052139091431/50000000000000000000)
  centralHi := (271521652104278182863/100000000000000000000)
  directionLo := (34501239669791039973/12500000000000000000)
  directionHi := (55201983471665663957/20000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree032.table
  base := (-1941312987105810748395239042319362862787/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-245485253164191809348904095111112000000000000)
      constant := (2325979916342021413262972581986633620692439837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree032.table
  base := (-2482374728104893466372538655187744514467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-15271692998207673000465867177320000000000000)
      constant := (145812773943568783864244983417142732607387828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34501239669791039973/12500000000000000000)
  centralHi := (55201983471665663957/20000000000000000000)
  directionLo := (280426356462558248777/100000000000000000000)
  directionHi := (140213178231279124389/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree033.table
  base := (-9775427447324726852991774430788399085161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-140239656535412276339713777956360000000000000)
      constant := (1369390362190623138315067496168136431955548479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree033.table
  base := (-9998042835449090777895114073641141837707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-15704162690708409326201255911680000000000000)
      constant := (154530560381240714422945207696063835967852997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280426356462558248777/100000000000000000000)
  centralHi := (140213178231279124389/50000000000000000000)
  directionLo := (284774311196744605987/100000000000000000000)
  directionHi := (71193577799186151497/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree034.table
  base := (-2454501469921596611706881687643936571279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1296887551816461927370327527658920000000000000)
      constant := (13039715766790242043801801095509699847429064516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree034.table
  base := (-10040217768068248403243785651343194200343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-16136632383209145651936644646040000000000000)
      constant := (163506735406253184706870384502119450268018553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284774311196744605987/100000000000000000000)
  centralHi := (71193577799186151497/25000000000000000000)
  directionLo := (57811374395111865747/20000000000000000000)
  directionHi := (9033027249236229023/3125000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree035.table
  base := (-9835403593090088127731178186054689013609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1331618194814213367683231053710600000000000000)
      constant := (13775459825040969956627032987901742630455867959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree035.table
  base := (-5028561064431281519203964739621384864177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-16569102075709881977672033380400000000000000)
      constant := (172740717955174456594975352728980574813700734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57811374395111865747/20000000000000000000)
  centralHi := (9033027249236229023/3125000000000000000)
  directionLo := (58655380709704528111/20000000000000000000)
  directionHi := (73319225887130660139/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree036.table
  base := (-9828620625217434724119680733999178785617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-151816537534662756444014953306920000000000000)
      constant := (1614633620428130331524051685175509909801677463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree036.table
  base := (-1004975262285013236575263972291695262797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-3400314353642123660681484422952000000000000)
      constant := (36446396154209991282657795512611386411960774) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58655380709704528111/20000000000000000000)
  centralHi := (73319225887130660139/25000000000000000000)
  directionLo := (297437067417166429339/100000000000000000000)
  directionHi := (14871853370858321467/5000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree037.table
  base := (-4899284618664145987649678409080799838961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1401079480809716248309038105813960000000000000)
      constant := (15308404953744127138006561022007873615400720222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree037.table
  base := (-10019019560155535662222911879103977761799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-17434041460711354629142810849120000000000000)
      constant := (191980042299823781724307356386573995764008329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297437067417166429339/100000000000000000000)
  centralHi := (14871853370858321467/5000000000000000000)
  directionLo := (6030796829356418083/2000000000000000000)
  directionHi := (301539841467820904151/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree038.table
  base := (-974608679021511530839709721673890193941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-287162024761493537724388326373128000000000000)
      constant := (3221106210928247299380072082246326958159644182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree038.table
  base := (-4982879763477198485209843493322497213603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-17866511153212090954878199583480000000000000)
      constant := (201984459987409027409494591389984797948008026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6030796829356418083/2000000000000000000)
  centralHi := (301539841467820904151/100000000000000000000)
  directionLo := (30558753723140137099/10000000000000000000)
  directionHi := (305587537231401370991/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree039.table
  base := (-386877856991605233061092429825433702833/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (29348)
      previous := (0)
      next := (23023)
      square := (688624818058864764824811292404000000000000)
      linear := (-32678683706782647309663225731496000000000000)
      constant := (376067727960656735202344756242181550704060435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree039.table
  base := (-9890745883013205474964492955010234303993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-18298980845712827280613588317840000000000000)
      constant := (212244824726489220690185894309179586053187703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30558753723140137099/10000000000000000000)
  centralHi := (305587537231401370991/100000000000000000000)
  directionLo := (61916463022323125869/20000000000000000000)
  directionHi := (154791157555807814673/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree040.table
  base := (-9576865936107973845930625704877657867117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1505271409802970569247748683969000000000000000)
      constant := (17760924307708780830956427198979697238051903667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree040.table
  base := (-9794697473459499155506867623795149804153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-18731450538213563606348977052200000000000000)
      constant := (222760756247991893975146659627012365753603063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61916463022323125869/20000000000000000000)
  centralHi := (154791157555807814673/50000000000000000000)
  directionLo := (12541047914657354063/4000000000000000000)
  directionHi := (39190774733304231447/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree041.table
  base := (-9461515159398888623336347743215332920797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1540002052800722009560652210020680000000000000)
      constant := (18619132001309139001296505897732886199676769347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree041.table
  base := (-9678285871920983497645538434108197916937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-19163920230714299932084365786560000000000000)
      constant := (233531899289467991062495160527136763301940327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12541047914657354063/4000000000000000000)
  centralHi := (39190774733304231447/12500000000000000000)
  directionLo := (158710541290817216459/50000000000000000000)
  directionHi := (317421082581634432919/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree042.table
  base := (-9326522129408365629293310743971243279283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-174970299533163716652617304008040000000000000)
      constant := (2166404880929979785994800349343472910747333637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree042.table
  base := (-4771070707376283809689505582628234282329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-19596389923215036257819754520920000000000000)
      constant := (244557920402985765028810187452299328129295918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158710541290817216459/50000000000000000000)
  centralHi := (317421082581634432919/100000000000000000000)
  directionLo := (321268751337585495579/100000000000000000000)
  directionHi := (16063437566879274779/5000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree043.table
  base := (-1834495645511024861338727737859902530261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-321892667759244978037291852424808000000000000)
      constant := (4079286949757681467903606863508697036480846411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree043.table
  base := (-4693429119619631614783762568901559904871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-20028859615715772583555143255280000000000000)
      constant := (255838505289921444680104673801922149620646482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321268751337585495579/100000000000000000000)
  centralHi := (16063437566879274779/5000000000000000000)
  directionLo := (32507088073945641851/10000000000000000000)
  directionHi := (325070880739456418511/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree044.table
  base := (-8999942493161457188146883694839675037017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1644193981793976330499362788175720000000000000)
      constant := (21315480508288985885261212719486534764338858567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree044.table
  base := (-460649925021165107735177460384163658029/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-4092265861643301781858106397928000000000000)
      constant := (53474671314051537876032820710243109699610636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32507088073945641851/10000000000000000000)
  centralHi := (325070880739456418511/100000000000000000000)
  directionLo := (20551815653466344583/6250000000000000000)
  directionHi := (328829050455461513329/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree045.table
  base := (-440472262184544600852126359532333047339/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (29348)
      previous := (0)
      next := (23023)
      square := (688624818058864764824811292404000000000000)
      linear := (-37309436106482839351383695871720000000000000)
      constant := (494550188517745755797916499113866249446476084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree045.table
  base := (-4510547954973503297030149009308046935119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-20893799000717245235025920724000000000000000)
      constant := (279162191910535710685572946153652086342644098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20551815653466344583/6250000000000000000)
  centralHi := (328829050455461513329/100000000000000000000)
  directionLo := (13301790035459438687/4000000000000000000)
  directionHi := (41568093860810745897/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree046.table
  base := (-4300745561632302559972420577812612677021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18630000000000000000000000000000000000000000
      center := (57420)
      previous := (0)
      next := (45045)
      square := (1347309426636909322483326441660000000000000)
      linear := (-74506750773455617875007384359960000000000000)
      constant := (1009315089144399062262442219540510205165419754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree046.table
  base := (-8811658714729506040689798829403101925739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 230000000000000000000000000000000000000000
      center := (715)
      previous := (0)
      next := (550)
      square := (16633449711566781759053412860000000000000)
      linear := (-927229073618173111337448237320000000000000)
      constant := (12661075758614577786717681703883728655708003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13301790035459438687/4000000000000000000)
  centralHi := (41568093860810745897/12500000000000000000)
  directionLo := (336219390072716605089/100000000000000000000)
  directionHi := (33621939007271660509/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree047.table
  base := (-1047070209710002768000711409629577358503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1748385910787230651438073366330760000000000000)
      constant := (24193925575600970257096188194576337918124039624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree047.table
  base := (-8585172212353494700474965980231511128423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-21758738385718717886496698192720000000000000)
      constant := (303500751460635179372053240972277530613064233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336219390072716605089/100000000000000000000)
  centralHi := (33621939007271660509/10000000000000000000)
  directionLo := (339854299928048756449/100000000000000000000)
  directionHi := (6797085998560975129/2000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree048.table
  base := (-8135117536878123715242185705979361033121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-198124061531664676861219654709160000000000000)
      constant := (2799308257956177045249120758710152262121310919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree048.table
  base := (-8342100882874896548627155280616322230469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-22191208078219454212232086927080000000000000)
      constant := (316049973238085797735325824279273965540081899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339854299928048756449/100000000000000000000)
  centralHi := (6797085998560975129/2000000000000000000)
  directionLo := (171725370940273904499/50000000000000000000)
  directionHi := (343450741880547808999/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree049.table
  base := (-6154375212197957597556371687223782077/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-363569439356546706412776083686824000000000000)
      constant := (5242754873493957869002214819353285929416352512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree049.table
  base := (-2020722550672704139540603846267855008269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-22623677770720190537967475661440000000000000)
      constant := (328852172123473075653598939372077218802502796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171725370940273904499/50000000000000000000)
  centralHi := (343450741880547808999/100000000000000000000)
  directionLo := (347009911986694167563/100000000000000000000)
  directionHi := (86752477996673541891/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree050.table
  base := (-152088679588255233474300899457528423279/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-370515567956096994475356788897160000000000000)
      constant := (5450781508207725127969307532735443645909181290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree050.table
  base := (-7807968194546159666759201116080123335053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-23056147463220926863702864395800000000000000)
      constant := (341907121692764958414840683649593614755756963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (347009911986694167563/100000000000000000000)
  centralHi := (86752477996673541891/25000000000000000000)
  directionLo := (87633236394549452743/25000000000000000000)
  directionHi := (350532945578197810973/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree051.table
  base := (-3658013322655826887615975243898187910343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-209700942530915156965520830059720000000000000)
      constant := (3146017373395702260255986997520081454717713954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree051.table
  base := (-7517746758268124193877335089769674807759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-23488617155721663189438253130160000000000000)
      constant := (355214604050952858108056810947891842026695489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87633236394549452743/25000000000000000000)
  centralHi := (350532945578197810973/100000000000000000000)
  directionLo := (354020921492561430857/100000000000000000000)
  directionHi := (177010460746280715429/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree052.table
  base := (-7012771314953197633463927713140299618257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1922039125775987853002590996589160000000000000)
      constant := (29394503984425110734885554855568131301657305807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree052.table
  base := (-721262281901657268018842739678073558123/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-4784217369644479903034728372904000000000000)
      constant := (73754881844925441489846407905804598175505866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354020921492561430857/100000000000000000000)
  centralHi := (177010460746280715429/50000000000000000000)
  directionLo := (357474865932077663617/100000000000000000000)
  directionHi := (178737432966038831809/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree053.table
  base := (-1673761777782063603125267408633861756757/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-1956769768773739293315494522640840000000000000)
      constant := (30494934167597531207571456902998270630338877228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree053.table
  base := (-6892979323422022643630329012328241692103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-24353556540723135840909030598880000000000000)
      constant := (382586334635020462671377246227098360144877513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357474865932077663617/100000000000000000000)
  centralHi := (178737432966038831809/50000000000000000000)
  directionLo := (360895755990384923751/100000000000000000000)
  directionHi := (45111969498798115469/12500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree054.table
  base := (-1272644023893700227965592305956425185313/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (29348)
      previous := (0)
      next := (23023)
      square := (688624818058864764824811292404000000000000)
      linear := (-44255564706033127413964401082056000000000000)
      constant := (702565138303896667364686713897837459692724807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree054.table
  base := (-1639796527175642309747769999964666147327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-24786026233223872166644419333240000000000000)
      constant := (396650184638244251437609557848554766432256068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360895755990384923751/100000000000000000000)
  centralHi := (45111969498798115469/12500000000000000000)
  directionLo := (364284522880928900083/100000000000000000000)
  directionHi := (91071130720232225021/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree055.table
  base := (-3008822082290142006380518688460231937593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2026231054769242173941301574744200000000000000)
      constant := (32755979991628009878195078643256335043412155086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree055.table
  base := (-6211600665502817924422955607959780720949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-25218495925724608492379808067600000000000000)
      constant := (410965770121747577460566420786889275998617979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364284522880928900083/100000000000000000000)
  centralHi := (91071130720232225021/25000000000000000000)
  directionLo := (367642054897560063003/100000000000000000000)
  directionHi := (91910513724390015751/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree056.table
  base := (-5658661494255588480201099474164378333737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2060961697766993614254205100795880000000000000)
      constant := (33916565806479871963424035978883050552777703287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree056.table
  base := (-146264220290381687858738572558971472381/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-5130193123645068963623039360392000000000000)
      constant := (85106581629583641773483551496866432728883608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367642054897560063003/100000000000000000000)
  centralHi := (91910513724390015751/25000000000000000000)
  directionLo := (370969200133939856537/100000000000000000000)
  directionHi := (185484600066969928269/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree057.table
  base := (-1057320677276349939686022830176165134551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (29348)
      previous := (0)
      next := (23023)
      square := (688624818058864764824811292404000000000000)
      linear := (-46570940905883223434824636152168000000000000)
      constant := (779937210517883152510805514600795277794402689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree057.table
  base := (-5476425290791127714356278428381066637299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-26083435310726081143850585536320000000000000)
      constant := (440351421637311755723908872008406415748868829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370969200133939856537/100000000000000000000)
  centralHi := (185484600066969928269/50000000000000000000)
  directionLo := (23391673061584068899/6250000000000000000)
  directionHi := (74853353797069020477/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree058.table
  base := (-4901790690681080470268031532208793757521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2130422983762496494880012152899240000000000000)
      constant := (36297792244012868195593683134802465396283982671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree058.table
  base := (-5089494308411494360189860645619693499279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-26515905003226817469585974270680000000000000)
      constant := (455421139085281618332929760873987182138881409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23391673061584068899/6250000000000000000)
  centralHi := (74853353797069020477/20000000000000000000)
  directionLo := (377535536453781042479/100000000000000000000)
  directionHi := (4719194205672263031/1250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree059.table
  base := (-4504534315353201113089814606951333494707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2165153626760247935192915678950920000000000000)
      constant := (37518405796498805430267141123075862311085299757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree059.table
  base := (-18760360055117870147053824734163340107/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-5389674939145510759064272601008000000000000)
      constant := (94148378861369291349912271786817379654169850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377535536453781042479/100000000000000000000)
  centralHi := (4719194205672263031/1250000000000000000)
  directionLo := (380776244274979410341/100000000000000000000)
  directionHi := (190388122137489705171/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree060.table
  base := (-2047567833495356987519284057407741410769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-244431585528666597278424356111400000000000000)
      constant := (4306555801754607460999004247429363486286657582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree060.table
  base := (-2139258468566975315843032668000605741299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-27380844388228290121056751739400000000000000)
      constant := (486313526205509891081758505033255359125705658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380776244274979410341/100000000000000000000)
  centralHi := (190388122137489705171/50000000000000000000)
  directionLo := (95997400720954857117/25000000000000000000)
  directionHi := (383989602883819428469/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree061.table
  base := (-3673887050730630137857786729913311938873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2234614912755750815818722731054280000000000000)
      constant := (40019568976908037563923747442876664496731230823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree061.table
  base := (-963767597028682587673857233592952850671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-27813314080729026446792140473760000000000000)
      constant := (502135878562472474162185934271697311767980164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95997400720954857117/25000000000000000000)
  centralHi := (383989602883819428469/100000000000000000000)
  directionLo := (9679407330823124243/2500000000000000000)
  directionHi := (387176293232924969721/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree062.table
  base := (-3241072036438318315943481405052233377229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2269345555753502256131626257105960000000000000)
      constant := (41300093929163355491022114097796196852019114579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree062.table
  base := (-3420036821275239435365216717028078683389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-28245783773229762772527529208120000000000000)
      constant := (518208799843275440070551175357812146376487219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9679407330823124243/2500000000000000000)
  centralHi := (387176293232924969721/100000000000000000000)
  directionLo := (195168484238812528537/50000000000000000000)
  directionHi := (15613478739105002283/4000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree063.table
  base := (-559393159151090605959923499268271159369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9522000000000000000000000000000000000000000
      center := (29348)
      previous := (0)
      next := (23023)
      square := (688624818058864764824811292404000000000000)
      linear := (-51201693305583415476545106292392000000000000)
      constant := (946679228482838818194601417335087761010244191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree063.table
  base := (-1486847086651199820797959113108003866641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-28678253465730499098262917942480000000000000)
      constant := (534532143019411407197982869323751731909093822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195168484238812528537/50000000000000000000)
  centralHi := (15613478739105002283/4000000000000000000)
  directionLo := (98368063884771887519/25000000000000000000)
  directionHi := (393472255539087550077/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree064.table
  base := (-2341835414043674640833965098417146057111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2338806841749005136757433309209320000000000000)
      constant := (43920971590260550619282634948939843708598850761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree064.table
  base := (-629078043956946619537893757860868940743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-29110723158231235423998306676840000000000000)
      constant := (551105765402847272100344838179246401321387812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98368063884771887519/25000000000000000000)
  centralHi := (393472255539087550077/100000000000000000000)
  directionLo := (198291378278110952893/50000000000000000000)
  directionHi := (396582756556221905787/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree065.table
  base := (-375188036118546679116715973962434405547/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-474707496949351315414067367052200000000000000)
      constant := (9052260348894998076856992261293283648156716597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree065.table
  base := (-2048152647072775506848088632948883531209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-29543192850731971749733695411200000000000000)
      constant := (567929528491743927105436470030670040611990439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198291378278110952893/50000000000000000000)
  centralHi := (396582756556221905787/100000000000000000000)
  directionLo := (49958631279484335963/12500000000000000000)
  directionHi := (79933810047174937541/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree066.table
  base := (-10933842655563242636056254945995312179/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-267585347527167557487026706812520000000000000)
      constant := (5180171661834844446141060162316750888795619968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree066.table
  base := (-784734882519517614284270267056393632883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-29975662543232708075469084145560000000000000)
      constant := (585003297825938489576290614762734335536409786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49958631279484335963/12500000000000000000)
  centralHi := (79933810047174937541/20000000000000000000)
  directionLo := (40273169310989255757/10000000000000000000)
  directionHi := (402731693109892557571/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree067.table
  base := (-456427473234397490496277758319475922413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2442998770742259457696143887364360000000000000)
      constant := (48001690750032961514324389325519217552401050726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree067.table
  base := (-270127581128883388386306676045285812273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-30408132235733444401204472879920000000000000)
      constant := (602326942850987595488394387807708175221230332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40273169310989255757/10000000000000000000)
  centralHi := (402731693109892557571/100000000000000000000)
  directionLo := (202885610353393000491/50000000000000000000)
  directionHi := (405771220706786000983/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree068.table
  base := (-416146904855604440460744325830010501077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2477729413740010898009047413416040000000000000)
      constant := (49401728949912739225123661518911789880039351627) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree068.table
  base := (-581513979808302235719180703261315121669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-30840601928234180726939861614280000000000000)
      constant := (619900336789763354043912982412294764300637099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202885610353393000491/50000000000000000000)
  centralHi := (405771220706786000983/100000000000000000000)
  directionLo := (40878814864497942299/10000000000000000000)
  directionHi := (408788148644979422991/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree069.table
  base := (18072320588202471057331569492063835603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 414000000000000000000000000000000000000000
      center := (1276)
      previous := (0)
      next := (1001)
      square := (29940209480820207166296143148000000000000)
      linear := (-2427497639360156848620242453592000000000000)
      constant := (49103043161852632988193697818276857213969821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree069.table
  base := (-36356737398253304764630787614010999619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 230000000000000000000000000000000000000000
      center := (715)
      previous := (0)
      next := (550)
      square := (16633449711566781759053412860000000000000)
      linear := (-1359698766118909437072836971680000000000000)
      constant := (27727102457424073338301227919229755494017526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40878814864497942299/10000000000000000000)
  centralHi := (408788148644979422991/100000000000000000000)
  directionLo := (205891486826983905183/50000000000000000000)
  directionHi := (411782973653967810367/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree070.table
  base := (606446501765136488809708189717776898963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2547190699735513778634854465519400000000000000)
      constant := (52261443316450813297601452384917217022343665587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree070.table
  base := (222832569166435970702613091104894695141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-31705541313235653378410639083000000000000000)
      constant := (655795882462351680547505554918388978587459178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205891486826983905183/50000000000000000000)
  centralHi := (411782973653967810367/100000000000000000000)
  directionLo := (414756174529106803979/100000000000000000000)
  directionHi := (20737808726455340199/5000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree071.table
  base := (565945048908632799697352892123885998647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2581921342733265218947757991571080000000000000)
      constant := (53721100553751138812932365577334352782312050606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree071.table
  base := (194680458105621129280539873905772595013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-6427602201147277940829205563472000000000000)
      constant := (134823559692505794270590872645612153702761877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414756174529106803979/100000000000000000000)
  centralHi := (20737808726455340199/5000000000000000000)
  directionLo := (104427053256308258283/25000000000000000000)
  directionHi := (417708213025233033133/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree072.table
  base := (52077527577257162561671827505215717777/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-290739109525668517695629057513640000000000000)
      constant := (6133401369053930195406503507517194625034761504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree072.table
  base := (47196396766354779617064336465946988577/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-32570480698237126029881416551720000000000000)
      constant := (692688991693379929013242321584015550622631456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104427053256308258283/25000000000000000000)
  centralHi := (417708213025233033133/100000000000000000000)
  directionLo := (210319767346918686583/50000000000000000000)
  directionHi := (420639534693837373167/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree073.table
  base := (442002668906057469411469195730178911913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-530276525745753619914713008734888000000000000)
      constant := (11339993962740822895536861464562818436196560137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree073.table
  base := (257013145483868667601829814438152139419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-33002950390737862355616805286080000000000000)
      constant := (711509352550099739005425097746922259854021208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210319767346918686583/50000000000000000000)
  centralHi := (420639534693837373167/100000000000000000000)
  directionLo := (105887642417022207873/25000000000000000000)
  directionHi := (423550569668088831493/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree074.table
  base := (1381143895084097501228752515349615467773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2686113271726519539886468569726120000000000000)
      constant := (58219164473726734743625437383335951346357210554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree074.table
  base := (522132481929917398007960004181401745317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-6687084016647719736270438804088000000000000)
      constant := (146115754910804605896897376380067961523272693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105887642417022207873/25000000000000000000)
  centralHi := (423550569668088831493/100000000000000000000)
  directionLo := (85288346679925066221/20000000000000000000)
  directionHi := (213220866699812665553/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree075.table
  base := (830777542490461181952833130591422025681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-302315990524918997799930232864200000000000000)
      constant := (6639798665192162108529980317158983041057068964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree075.table
  base := (634752176848548640659463435933709526879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-6773577955147867001417516550960000000000000)
      constant := (149979430851880531989258791687108932339718991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85288346679925066221/20000000000000000000)
  centralHi := (213220866699812665553/50000000000000000000)
  directionLo := (13416044604708898789/3125000000000000000)
  directionHi := (429313427350684761249/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree076.table
  base := (1946145956219828034956557256924342748517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2755574557722022420512275621829480000000000000)
      constant := (61317032272613301426278052099492222324862409866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree076.table
  base := (749042120333053656747384655284919066169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-6860071893648014266564594297832000000000000)
      constant := (153892878232730497240242507252021722186003401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13416044604708898789/3125000000000000000)
  centralHi := (429313427350684761249/100000000000000000000)
  directionLo := (432166039644840948237/100000000000000000000)
  directionHi := (216083019822420474119/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree077.table
  base := (279353110231193337142714576816674386011/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2790305200719773860825179147881160000000000000)
      constant := (62895689479131792342748316546232762892258965424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree077.table
  base := (4324826975985849106231144784482656542367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-34732829160740807658558360223520000000000000)
      constant := (789280387620814843606050181878411325310912143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432166039644840948237/100000000000000000000)
  centralHi := (216083019822420474119/50000000000000000000)
  directionLo := (43499994567933085427/10000000000000000000)
  directionHi := (434999945679330854271/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree078.table
  base := (2527502816339997155883392358731740926233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-313892871524169477904231408214760000000000000)
      constant := (7166016886140121647551965778430563637099590626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree078.table
  base := (4912430663451471397205456822057800431421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-35165298853241543984293748957880000000000000)
      constant := (809345048758044387610085971627988576428221709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43499994567933085427/10000000000000000000)
  centralHi := (434999945679330854271/100000000000000000000)
  directionLo := (87563101740341599143/20000000000000000000)
  directionHi := (109453877175426998929/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree079.table
  base := (5648186441739792680813657208597704718097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2859766486715276741450986199984520000000000000)
      constant := (66112412344797302565336923448567523049465738353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree079.table
  base := (2753923704984476192942454214128828786367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-35597768545742280310029137692240000000000000)
      constant := (829658282394925824527579956450528300855976286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87563101740341599143/20000000000000000000)
  centralHi := (109453877175426998929/25000000000000000000)
  directionLo := (55076635044166231027/12500000000000000000)
  directionHi := (440613080353329848217/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree080.table
  base := (6249023982218893593137013418341613498399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-2894497129713028181763889726036200000000000000)
      constant := (67750463380167560572630819613722519796792898751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree080.table
  base := (122218158072794268322169281690172310861/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-7206047647648603327152905285320000000000000)
      constant := (170043999793092961249884589711341011524454690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55076635044166231027/12500000000000000000)
  centralHi := (440613080353329848217/100000000000000000000)
  directionLo := (443393001181981289567/100000000000000000000)
  directionHi := (13856031286936915299/3125000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree081.table
  base := (6857354774720788126062861055971418751049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-325469752523419958008532583565320000000000000)
      constant := (7712033119604800871002413622852759924673744289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree081.table
  base := (3360723816039270098797532445853311899767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-36462707930743752961499915160960000000000000)
      constant := (871030111442609554416056267788892803989953486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443393001181981289567/100000000000000000000)
  centralHi := (13856031286936915299/3125000000000000000)
  directionLo := (446155601125749644009/100000000000000000000)
  directionHi := (44615560112574964401/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree082.table
  base := (1494603986772426462994225107735031118011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-592791683141706212477939355627912000000000000)
      constant := (14217181925108890691793925369725114348375653339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree082.table
  base := (366965337213811954784051860846342589299/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-7379035524648897857447060779064000000000000)
      constant := (178417707053035241118948566159054860918956684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446155601125749644009/100000000000000000000)
  centralHi := (44615560112574964401/10000000000000000000)
  directionLo := (28056324998131101341/6250000000000000000)
  directionHi := (448901199970097621457/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree083.table
  base := (809586503727391155496498774089249527447/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-599737811741256500540520060838248000000000000)
      constant := (14556658282125441505133861707972716506003153006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree083.table
  base := (7964329916790754648914938405947028365719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-37327647315745225612970692629680000000000000)
      constant := (913395188267063912446374824411765978005465351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28056324998131101341/6250000000000000000)
  centralHi := (448901199970097621457/100000000000000000000)
  directionLo := (451630107779926612527/100000000000000000000)
  directionHi := (28226881736245413283/6250000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree084.table
  base := (4362869999328380094308087576658404240647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-337046633522670438112833758915880000000000000)
      constant := (8277826333404847613340624847848621325179440734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree084.table
  base := (4298183112036111691233714260535972276227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-37760117008245961938706081364040000000000000)
      constant := (934949990608656797192767527811327058668248166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451630107779926612527/100000000000000000000)
  centralHi := (28226881736245413283/6250000000000000000)
  directionLo := (454342625308282828641/100000000000000000000)
  directionHi := (227171312654141414321/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree085.table
  base := (9362498944712163705672988361666206258703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3068150344701785383328407356294600000000000000)
      constant := (76237340145068748393908797052745035271979164847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree085.table
  base := (923526901274522949442959909549991834917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-7638517340149339652888294019680000000000000)
      constant := (191350572942063852974942225683003891361342186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454342625308282828641/100000000000000000000)
  centralHi := (227171312654141414321/50000000000000000000)
  directionLo := (457039044383231267139/100000000000000000000)
  directionHi := (22851952219161563357/5000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree086.table
  base := (10006000095787183668526807237505310344683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3102880987699536823641310882346280000000000000)
      constant := (77993994768786218388085737042302585042959321867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree086.table
  base := (9880895779686719477964051331136820540809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-38625056393247434590176858832760000000000000)
      constant := (978803735187899220187088642258651378066087961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457039044383231267139/100000000000000000000)
  centralHi := (22851952219161563357/5000000000000000000)
  directionLo := (459719648274306191679/100000000000000000000)
  directionHi := (1436623900857206849/312500000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree087.table
  base := (1332013206260495832025603469134376942093/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-348623514521920918217134934266440000000000000)
      constant := (8863377218569644697929019991058310148970438184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree087.table
  base := (2633277013437764195325234329807720878667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-39057526085748170915912247567120000000000000)
      constant := (1001102528790160621394013819798493137379259372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459719648274306191679/100000000000000000000)
  centralHi := (1436623900857206849/312500000000000000)
  directionLo := (92476942407968128411/20000000000000000000)
  directionHi := (57798089004980080257/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree088.table
  base := (11312681671297004984746320239370471202533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3172342273695039704267117934449640000000000000)
      constant := (81566535001053745374985092378824465320557336517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree088.table
  base := (2797942820251228062413023733163445194117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-39489995778248907241647636301480000000000000)
      constant := (1023649174338072737372603723269293850030751572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92476942407968128411/20000000000000000000)
  centralHi := (57798089004980080257/12500000000000000000)
  directionLo := (93006900571276087949/20000000000000000000)
  directionHi := (232517251428190219873/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree089.table
  base := (11975597979551221882856127205495220344521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3207072916692791144580021460501320000000000000)
      constant := (83382409292489580504384248216874184696542380329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree089.table
  base := (1185675471334438847531338354896051152069/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-7984493094149928713476605007168000000000000)
      constant := (209288720533177721278836572456356022118889002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93006900571276087949/20000000000000000000)
  centralHi := (232517251428190219873/50000000000000000000)
  directionLo := (467669280331299356489/100000000000000000000)
  directionHi := (46766928033129935649/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree090.table
  base := (6322364022761358771554622841762869866461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-360200395521171398321436109617000000000000000)
      constant := (9468668046642145320745588164611266046868441642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree090.table
  base := (6263965650187606484293401498197036123809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-40354935163250379893118413770200000000000000)
      constant := (1069485746563949658311700994745092464218989922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467669280331299356489/100000000000000000000)
  centralHi := (46766928033129935649/10000000000000000000)
  directionLo := (470289296799650777363/100000000000000000000)
  directionHi := (117572324199912694341/25000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree091.table
  base := (332998722190791289030527808805922825773/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-655306840537658805041165702520936000000000000)
      constant := (17414667822657042588096007783790983897292378216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree091.table
  base := (6602588792222105543212707744257312441727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-40787404855751116218853802504560000000000000)
      constant := (1092775540723157363738986290570204236563347166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470289296799650777363/100000000000000000000)
  centralHi := (117572324199912694341/25000000000000000000)
  directionLo := (236447398803108307037/50000000000000000000)
  directionHi := (18915791904248664563/4000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree092.table
  base := (14001140972203431856174259632077336950279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 18630000000000000000000000000000000000000000
      center := (57420)
      previous := (0)
      next := (45045)
      square := (1347309426636909322483326441660000000000000)
      linear := (-143968036768958498500814436463320000000000000)
      constant := (3867321054396037959548433350474720078738369777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree092.table
  base := (13888373598716755077675620212838535151013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 230000000000000000000000000000000000000000
      center := (715)
      previous := (0)
      next := (550)
      square := (16633449711566781759053412860000000000000)
      linear := (-1792168458619645762808225706040000000000000)
      constant := (48535344420915487156333847605535286308473299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236447398803108307037/50000000000000000000)
  centralHi := (18915791904248664563/4000000000000000000)
  directionLo := (475486021373645778847/100000000000000000000)
  directionHi := (14858938167926430589/3125000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree093.table
  base := (7344094058250140074138911267950671239201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-371777276520421878425737284967560000000000000)
      constant := (10093682539437350801400622670395346291539671922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree093.table
  base := (14577402768200621836169043287404236587893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-41652344240752588870324579973280000000000000)
      constant := (1140097827769475294858614538032856841154995397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475486021373645778847/100000000000000000000)
  centralHi := (14858938167926430589/3125000000000000000)
  directionLo := (478063200257511649227/100000000000000000000)
  directionHi := (119515800064377912307/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree094.table
  base := (192262217431630928451790917043916872217/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-676145226336309669228907818151944000000000000)
      constant := (18551522017200249213312322562689580704922019728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree094.table
  base := (15272151813621796570742612622460918709449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-42084813933253325196059968707640000000000000)
      constant := (1164130199063678680703269154751361825997298521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478063200257511649227/100000000000000000000)
  centralHi := (119515800064377912307/25000000000000000000)
  directionLo := (60078320023632516523/12500000000000000000)
  directionHi := (96125312037812026437/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree095.table
  base := (16079399045547232021866418450989420614311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3415456774679299786457442616811400000000000000)
      constant := (94691781241165900760227016606282445683902612039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree095.table
  base := (3194502131612466081885452178420135194391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-8503456725150812304359071488400000000000000)
      constant := (237681995466595353435274141693484251517832839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60078320023632516523/12500000000000000000)
  centralHi := (96125312037812026437/20000000000000000000)
  directionLo := (241588160553183357841/50000000000000000000)
  directionHi := (483176321106366715683/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree096.table
  base := (16783346385153386327229897295451460737729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-383354157519672358530038460318120000000000000)
      constant := (10738405749901154120258251081319324404572327769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree096.table
  base := (833918616813723917930155930692681343371/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-8589950663650959569506149235272000000000000)
      constant := (242587421198550699435258857644961713722573036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241588160553183357841/50000000000000000000)
  centralHi := (483176321106366715683/100000000000000000000)
  directionLo := (242856348587285933389/50000000000000000000)
  directionHi := (485712697174571866779/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree097.table
  base := (17492715718931780067164355679708279748799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3484918060674802667083249668914760000000000000)
      constant := (98619217166632624267201245431369900078956288351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree097.table
  base := (8694816453294538917718882336140712297333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-43382223010755534173266134910720000000000000)
      constant := (1237711530057865883696721543253456873610578314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242856348587285933389/50000000000000000000)
  centralHi := (485712697174571866779/100000000000000000000)
  directionLo := (244117948497909463559/50000000000000000000)
  directionHi := (488235896995818927119/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree098.table
  base := (18207406258524740179247896842219557372673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3519648703672554107396153194966440000000000000)
      constant := (100612473175052274381806257850435145813861665377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree098.table
  base := (4526547841334883422677714849931226699141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-43814692703256270499001523645080000000000000)
      constant := (1262733196097374297903714913869174475695382356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244117948497909463559/50000000000000000000)
  centralHi := (488235896995818927119/100000000000000000000)
  directionLo := (490746123809476935361/100000000000000000000)
  directionHi := (245373061904738467681/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree099.table
  base := (18927320040089126261843327643797748334309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-394931038518922838634339635668680000000000000)
      constant := (11402823952968513633674393877805401079819645149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree099.table
  base := (18827949563725900374649749905690683695713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-44247162395757006824736912379440000000000000)
      constant := (1288002052190563568601444666692890371675032177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490746123809476935361/100000000000000000000)
  centralHi := (245373061904738467681/50000000000000000000)
  directionLo := (61655446960399033749/12500000000000000000)
  directionHi := (493243575683192269993/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree100.table
  base := (4913090461264082452476912707250707712591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3589109989668056988021960247069800000000000000)
      constant := (104658040291605222925158519191411942299107247036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree100.table
  base := (4888703031761608756425804778748167323357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-44679632088257743150472301113800000000000000)
      constant := (1313518047884216473816150207891831122056223412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61655446960399033749/12500000000000000000)
  centralHi := (493243575683192269993/100000000000000000000)
  directionLo := (495728445695277382233/100000000000000000000)
  directionHi := (247864222847638691117/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree101.table
  base := (2038243912312926223928548632512090744857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-724768126533161685666972754624296000000000000)
      constant := (21342068670806079019866141368637885152652755186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree101.table
  base := (10143343188113334837750857156192462321137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-45112101780758479476207689848160000000000000)
      constant := (1339281134151102619992564044079631625135762946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495728445695277382233/100000000000000000000)
  centralHi := (247864222847638691117/50000000000000000000)
  directionLo := (498200922108911930429/100000000000000000000)
  directionHi := (49820092210891193043/10000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree102.table
  base := (21117461917450842218131379121397384405619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-406507919518173318738640811019240000000000000)
      constant := (12086924545492307794177540217091692947155152059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree102.table
  base := (5255870562894635997627262965330263281467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-45544571473259215801943078582520000000000000)
      constant := (1365291263349647023214245534112558837103584172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498200922108911930429/100000000000000000000)
  centralHi := (49820092210891193043/10000000000000000000)
  directionLo := (250330594269300555309/50000000000000000000)
  directionHi := (500661188538601110619/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree103.table
  base := (21857342791880800277541676107437478922029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3693301918661311308960670825224840000000000000)
      constant := (110873969211255173663486931891192068534330020621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree103.table
  base := (136031951492027969258870449079489121009/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-9195408233151990425535693463376000000000000)
      constant := (278309677836948788426550365039741591840440352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250330594269300555309/50000000000000000000)
  centralHi := (500661188538601110619/100000000000000000000)
  directionLo := (503109424109307699873/100000000000000000000)
  directionHi := (251554712054653849937/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree104.table
  base := (11300998380159890974640923826326129361181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3728032561659062749273574351276520000000000000)
      constant := (112985284617934234407388535295148816633994489338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree104.table
  base := (11255745648311718634516824160966462698249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-46409510858260688453413856051240000000000000)
      constant := (1418052466669682674163786791302782517534747442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503109424109307699873/100000000000000000000)
  centralHi := (251554712054653849937/50000000000000000000)
  directionLo := (20221832144345924211/4000000000000000000)
  directionHi := (126386450902162026319/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree105.table
  base := (11675670609010883607095962325572594374789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-418084800517423798842941986369800000000000000)
      constant := (12790695954437465574166854072164102243636740858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree105.table
  base := (23262536787638198583322902548043409159461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-46841980550761424779149244785600000000000000)
      constant := (1444803452089153123595204943981414963445354869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20221832144345924211/4000000000000000000)
  centralHi := (126386450902162026319/25000000000000000000)
  directionLo := (63496312204064796797/12500000000000000000)
  directionHi := (507970497632518374377/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree106.table
  base := (753290496088679641565415123188256419601/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3797493847654565629899381403379880000000000000)
      constant := (117266902686911446119651574130355315178351463968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree106.table
  base := (12009084204792412955735701588698483145107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-47274450243262161104884633519960000000000000)
      constant := (1471801302963299989810326814248522995167523206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63496312204064796797/12500000000000000000)
  centralHi := (507970497632518374377/100000000000000000000)
  directionLo := (510383672724493520463/100000000000000000000)
  directionHi := (31898979545280845029/6250000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree107.table
  base := (4972756538067086908604358848548145314571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-766444898130463414042456985886312000000000000)
      constant := (23887439712980503802322437735291615478584052779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree107.table
  base := (4955661625941487737943357447627760856573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-9541383987152579486124004450864000000000000)
      constant := (299809195602559082398184422418399085493127117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (510383672724493520463/100000000000000000000)
  centralHi := (31898979545280845029/6250000000000000000)
  directionLo := (10255709830186450179/2000000000000000000)
  directionHi := (512785491509322508951/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree108.table
  base := (6406681452685370565541537406763683423267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-429661681516674278947243161720360000000000000)
      constant := (13514127552628008318841139626683527587112696748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree108.table
  base := (12771440060261485833273601839828153701019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-48139389628263633756355410988680000000000000)
      constant := (1526537437124900848618941068306058186615678102) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10255709830186450179/2000000000000000000)
  centralHi := (512785491509322508951/100000000000000000000)
  directionLo := (257588056410410856749/50000000000000000000)
  directionHi := (515176112820821713499/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree109.table
  base := (26394051507654415897253359390989433556659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3901685776647819950838091981534920000000000000)
      constant := (123836747753971838857388370642761626238469281491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree109.table
  base := (26311810697482408886592057760266240797713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-48571859320764370082090799723040000000000000)
      constant := (1554275641320489870253992638272360841381990177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257588056410410856749/50000000000000000000)
  centralHi := (515176112820821713499/100000000000000000000)
  directionLo := (517555691824451466393/100000000000000000000)
  directionHi := (258777845912225733197/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree110.table
  base := (27165688118477973289416074891575961355603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-3936416419645571391150995507586600000000000000)
      constant := (126065994835191223737821223662285138368126232947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree110.table
  base := (3385628532299572594768472204781200089879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-49004329013265106407826188457400000000000000)
      constant := (1582260552722004406182065632486634038780367928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517555691824451466393/100000000000000000000)
  centralHi := (258777845912225733197/50000000000000000000)
  directionLo := (519924380134843392223/100000000000000000000)
  directionHi := (16247636879213856007/3125000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree111.table
  base := (13970782994263068688003221231947302131139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-441238562515924759051544337070920000000000000)
      constant := (14257209581408509818416824201892682210892705558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree111.table
  base := (27862463224576179947494243489207025802029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-49436798705765842733561577191760000000000000)
      constant := (1610492134522317812823622107561770516649273341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519924380134843392223/100000000000000000000)
  centralHi := (16247636879213856007/3125000000000000000)
  directionLo := (52228232592853043047/10000000000000000000)
  directionHi := (522282325928530430471/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree112.table
  base := (14360808707376282976425463966572594392347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-4005877705641074271776802559689960000000000000)
      constant := (130583419045420100024072321341152618194235353206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree112.table
  base := (7161011995909288776585224480023809880967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-49869268398266579059296965926120000000000000)
      constant := (1638970350954478927015416358636850381708126172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52228232592853043047/10000000000000000000)
  centralHi := (522282325928530430471/100000000000000000000)
  directionLo := (104925934810423346687/20000000000000000000)
  directionHi := (131157418513029183359/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree113.table
  base := (1180231063642341315821813431253136705787/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-808121669727765142417941217148328000000000000)
      constant := (26574318090739246879415867772177964273531335815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree113.table
  base := (1839357302120255536495948777671901987759/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-50301738090767315385032354660480000000000000)
      constant := (1667695167262312032820200281213634978424392176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104925934810423346687/20000000000000000000)
  centralHi := (131157418513029183359/25000000000000000000)
  directionLo := (16467705191440965319/3125000000000000000)
  directionHi := (526966566126110890209/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree114.table
  base := (15146989777567421043581993171010539969531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-452815443515175239155845512421480000000000000)
      constant := (15019933079642667193373146880913242361589874182) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree114.table
  base := (3777425741313194900168302304413635067681/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-50734207783268051710767743394840000000000000)
      constant := (1696666549671848408434319549475158503606425992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16467705191440965319/3125000000000000000)
  centralHi := (526966566126110890209/100000000000000000000)
  directionLo := (529293140644633101481/100000000000000000000)
  directionHi := (264646570322316550741/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree115.table
  base := (1554308206839723757100973123633930347631/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3726000000000000000000000000000000000000000
      center := (11484)
      previous := (0)
      next := (9009)
      square := (269461885327381864496665288332000000000000)
      linear := (-35739735953341987762743592503000000000000000)
      constant := (1195711636267417978287834351356520048950546212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree115.table
  base := (31013053232696837268141437478634553119363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 230000000000000000000000000000000000000000
      center := (715)
      previous := (0)
      next := (550)
      square := (16633449711566781759053412860000000000000)
      linear := (-2224638151120382088543614440400000000000000)
      constant := (75038455015807210080501522354508594721745349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (529293140644633101481/100000000000000000000)
  centralHi := (264646570322316550741/50000000000000000000)
  directionLo := (106321906614238989209/20000000000000000000)
  directionHi := (265804766535597473023/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree116.table
  base := (15941134953876994363141994202151966230191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-4144800277632080033028416663896680000000000000)
      constant := (139853909226311905421896037930305939201994908318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree116.table
  base := (31810598453066559275060837369121944289599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-51599147168269524362238520863560000000000000)
      constant := (1755348882445413111775448452541545508529197871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106321906614238989209/20000000000000000000)
  centralHi := (265804766535597473023/50000000000000000000)
  directionLo := (533915875930739175851/100000000000000000000)
  directionHi := (133478968982684793963/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree117.table
  base := (32682238132822889585282280532674055745189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-464392324514425719260146687772040000000000000)
      constant := (15802289818524037894586000363775581179402844829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree117.table
  base := (32611983007885286719747223634218643397209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-52031616860770260687973909597920000000000000)
      constant := (1785059769926597375238312802962721662357123561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533915875930739175851/100000000000000000000)
  centralHi := (133478968982684793963/25000000000000000000)
  directionLo := (21448491955924659817/4000000000000000000)
  directionHi := (268106149449058247713/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree118.table
  base := (8371502930615346925021933931831920644107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-4214261563627582913654223716000040000000000000)
      constant := (144606933145736683928713860419485543870717363372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree118.table
  base := (33417149968975069636747766548274420288869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-52464086553270997013709298332280000000000000)
      constant := (1815017097692112486708403518492357168332811701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21448491955924659817/4000000000000000000)
  centralHi := (268106149449058247713/50000000000000000000)
  directionLo := (16828091527598952213/3125000000000000000)
  directionHi := (538498928883166470817/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree119.table
  base := (3429353518666806244636970485826808007681/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-849798441325066870793425448410344000000000000)
      constant := (29402576237136372636376733076450129792642246338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree119.table
  base := (2139127751057519542283713644534910108503/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-52896556245771733339444687066640000000000000)
      constant := (1845220836477987596245822906844923479158369392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16828091527598952213/3125000000000000000)
  centralHi := (538498928883166470817/100000000000000000000)
  directionLo := (540775890112560524927/100000000000000000000)
  directionHi := (4224811641504379101/781250000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree120.table
  base := (8776188647540018779928426892421118266413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-475969205513676199364447863122600000000000000)
      constant := (16604272241719882717237551343723267776265569172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree120.table
  base := (17519305697800690933277475290034965366261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-53329025938272469665180075801000000000000000)
      constant := (1875670957847235417479082904224856993357504138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540775890112560524927/100000000000000000000)
  centralHi := (4224811641504379101/781250000000000000)
  directionLo := (21721732168342254629/4000000000000000000)
  directionHi := (271521652104278182863/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree121.table
  base := (35919617508809625432275752759143873035031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-4318453492620837234592934294155080000000000000)
      constant := (151883637868806475633942923378513675815678043319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree121.table
  base := (35854799868013495164513554407047657810413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-53761495630773205990915464535360000000000000)
      constant := (1906367434166480420707816962700908210981708477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21721732168342254629/4000000000000000000)
  centralHi := (271521652104278182863/50000000000000000000)
  directionLo := (68162661283100640057/12500000000000000000)
  directionHi := (545301290264805120457/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree122.table
  base := (7347614597460276223656693255551989792053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-870636827123717734981167564041352000000000000)
      constant := (30869688416456030009208493755471563210599678997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree122.table
  base := (183372793366672555505618717628923220999/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-10838793064654788463330170653944000000000000)
      constant := (387462047716649538618953977207492015356338840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68162661283100640057/12500000000000000000)
  centralHi := (545301290264805120457/100000000000000000000)
  directionLo := (4380399719354759001/800000000000000000)
  directionHi := (273774982459672437563/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree123.table
  base := (18780035748988305005992537939600611299899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-487546086512926679468749038473160000000000000)
      constant := (17425873410409924297429588955673197020797638278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree123.table
  base := (37497838485206268594242752900207037889691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-54626435015774678642386242004080000000000000)
      constant := (1968499345003893767427488151530429523043646539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4380399719354759001/800000000000000000)
  centralHi := (273774982459672437563/50000000000000000000)
  directionLo := (549789442424907209283/100000000000000000000)
  directionHi := (137447360606226802321/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree124.table
  base := (3838556490083071416176374460610618819003/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85698000000000000000000000000000000000000000
      center := (264132)
      previous := (0)
      next := (207207)
      square := (6197623362529782883423301631636000000000000)
      linear := (-884529084322818311106328974462024000000000000)
      constant := (31867378328056584901757117800566112811550919094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree124.table
  base := (2395286960699696167238689335568336800061/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-55058904708275414968121630738440000000000000)
      constant := (1999934728072161253981872487557530402675716304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549789442424907209283/100000000000000000000)
  centralHi := (137447360606226802321/25000000000000000000)
  directionLo := (552019834716656639569/100000000000000000000)
  directionHi := (55201983471665663957/10000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree125.table
  base := (39214506404631806895191633852161300907693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-4457376064611842995844548398361800000000000000)
      constant := (161860532917103472429773473526231259582593737357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree125.table
  base := (7830954150679685317053353167575164645727/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (3289)
      previous := (0)
      next := (2530)
      square := (76513868673207196091645699156000000000000)
      linear := (-11098274880155230258771403894560000000000000)
      constant := (406323272629667925445914600433147262097589583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552019834716656639569/100000000000000000000)
  centralHi := (55201983471665663957/10000000000000000000)
  directionLo := (554241251477476611959/100000000000000000000)
  directionHi := (13856031286936915299/2500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree126.table
  base := (40046850529128887339332275220936488990631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-499122967512177159573050213823720000000000000)
      constant := (18267086952818631922602833270771358624084394191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree126.table
  base := (39988331370164211543155035091238765897377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-55923844093276887619592408207160000000000000)
      constant := (2063544226289015021078270734858145307159712433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554241251477476611959/100000000000000000000)
  centralHi := (13856031286936915299/2500000000000000000)
  directionLo := (111290760040181956961/20000000000000000000)
  directionHi := (278226900100454892403/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree127.table
  base := (10220638267079763434685016221177804811071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-4526837350607345876470355450465160000000000000)
      constant := (166966638720892550792422578056549471033398325116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree127.table
  base := (20412614619446566274500119010131100655757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-56356313785777623945327796941520000000000000)
      constant := (2095718294227392373558709861706138704493790906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111290760040181956961/20000000000000000000)
  centralHi := (278226900100454892403/50000000000000000000)
  directionLo := (279328793125927398651/50000000000000000000)
  directionHi := (558657586251854797303/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree128.table
  base := (651899547730375905362124842276967933217/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (1320660)
      previous := (0)
      next := (1036035)
      square := (30988116812648914417116508158180000000000000)
      linear := (-4561567993605097316783258976516840000000000000)
      constant := (169549099512565444421775117919682931134106574912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree128.table
  base := (10416355404972880676117946597701547744841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-56788783478278360271063185675880000000000000)
      constant := (2128138544354173734881673501533856475028083556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell164.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279328793125927398651/50000000000000000000)
  centralHi := (558657586251854797303/100000000000000000000)
  directionLo := (112170542585023299511/20000000000000000000)
  directionHi := (140213178231279124389/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 116
  qDenominator := 207
  table := BinomialMassData.Q116_207.Degree129.table
  base := (42563862724787339541991074056845928676901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (146740)
      previous := (0)
      next := (115115)
      square := (3443124090294323824124056462020000000000000)
      linear := (-510699848511427639677351389174280000000000000)
      constant := (19127907017873018021605246782665123466430725661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q116_207.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree129.table
  base := (42508866981246162750278707000858128534351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (16445)
      previous := (0)
      next := (12650)
      square := (382569343366035980458228495780000000000000)
      linear := (-57221253170779096596798574410240000000000000)
      constant := (2160804954698977012058996729517433949994671679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell164.Kernel129
