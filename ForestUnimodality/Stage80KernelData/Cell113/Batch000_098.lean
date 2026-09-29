import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell113.Parameters
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch000_049
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch050_099
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch000_049
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree000.table
  base := (448444219519534119935855187/12500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (329290669316359072005262475000000000000)
      linear := (-18109573223172726729596204750000000000)
      constant := (89688843903906823987171037400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree000.table
  base := (448444219519534119935855187/12500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (9)
      square := (329290669316359072005262475000000000000)
      linear := (-18109573223172726729596204750000000000)
      constant := (89688843903906823987171037400000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree001.table
  base := (4030528955576686084393662065337988871157/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-409358421516803875676040156022597250000000000)
      constant := (57330437889537140562502533687966219572265398025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree001.table
  base := (100676788546880637247832978957560643751689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-409788557453598369713847030130566000000000000)
      constant := (57281590859645776038531124184020869767577853717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9991688896166689071/20000000000000000000)
  directionHi := (12489611120208361339/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree002.table
  base := (58899504253850588034027327613610712829451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-798149692066611146568917524733391000000000000)
      constant := (33871833995236607126743507526225320018592238703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree002.table
  base := (117615884392784679327520618383243509342103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-1598019927880400269289062545898657000000000000)
      constant := (67641517410577675690853915684612665510441214859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9991688896166689071/20000000000000000000)
  centralHi := (12489611120208361339/25000000000000000000)
  directionLo := (35325954869928977883/50000000000000000000)
  directionHi := (70651909739857955767/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree003.table
  base := (72129533224010947827991430670794856616197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-2373881925232836834923589786888369500000000000)
      constant := (42841981181343368803274268224283318885952315041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree003.table
  base := (1124703198420462279580074344314449739527/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-594115685213400949787607757884045500000000000)
      constant := (10690434143782815851898520410596630100159008496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35325954869928977883/50000000000000000000)
  centralHi := (70651909739857955767/100000000000000000000)
  directionLo := (43265282053956244873/50000000000000000000)
  directionHi := (86530564107912489747/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree004.table
  base := (46330791826393455334461361216880870089281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-3151464466332451376709344524309957000000000000)
      constant := (29628142176931392942760871765222768222808483693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree004.table
  base := (9244086412157728366520169065242100326637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-3154905553826807329011799517173707000000000000)
      constant := (29572727422961867147669210319489777483909001805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/50000000000000000000)
  centralHi := (86530564107912489747/100000000000000000000)
  directionLo := (99916888961666890711/100000000000000000000)
  directionHi := (12489611120208361339/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree005.table
  base := (1940290368607615428114792288767008705057/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-982261751858016479623774815432886125000000000)
      constant := (5697026000664138133044920864554317975989680484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree005.table
  base := (30964518549454413520754859797384089856501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-3933348366800010858873168002811232000000000000)
      constant := (22753907268661542824712001617855271639783662353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99916888961666890711/100000000000000000000)
  centralHi := (12489611120208361339/12500000000000000000)
  directionLo := (11171047790929277323/10000000000000000000)
  directionHi := (111710477909292773231/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree006.table
  base := (5358134344035777009668178107036969650791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-1176657387132920115070213499788283000000000000)
      constant := (4893569236855356955526361064934797092735621723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree006.table
  base := (5343418457174340309781875161419048115651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-1177947794943303597183634122112189250000000000)
      constant := (4889275055260673670244046549511648104616767303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11171047790929277323/10000000000000000000)
  centralHi := (111710477909292773231/100000000000000000000)
  directionLo := (61186348660602199773/50000000000000000000)
  directionHi := (122372697321204399547/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree007.table
  base := (7488430485621992566820863544590474669533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-2742106044815647501033304368287359750000000000)
      constant := (9278515647124490710499897073321373960955822649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree007.table
  base := (14932211517309901362298257818194761540003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-5490233992746417918595904974086282000000000000)
      constant := (18553766221477452732015851164998831737275323559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61186348660602199773/50000000000000000000)
  centralHi := (122372697321204399547/100000000000000000000)
  directionLo := (33044404995978161963/25000000000000000000)
  directionHi := (132177619983912647853/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree008.table
  base := (5176660782849024504836567308053885017617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-240838255028111905532783210538319500000000000)
      constant := (730167772610771098880924063627014001454528177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree008.table
  base := (1289755651736876504135120677499130087561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-1567169201429905362114318364930951750000000000)
      constant := (4748288635168328481290565164192197285223553066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/25000000000000000000)
  centralHi := (132177619983912647853/100000000000000000000)
  directionLo := (141303819479715911533/100000000000000000000)
  directionHi := (70651909739857955767/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree009.table
  base := (27415223588383032865472379702975582597/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-3519688585915262042819059105708947250000000000)
      constant := (10227082543957791965292403122480750023994280125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree009.table
  base := (341240108822625256830395297649067216033/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-1761779904673206244579660486340333000000000000)
      constant := (5118537324491811359705859172228435594754935745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141303819479715911533/100000000000000000000)
  centralHi := (70651909739857955767/50000000000000000000)
  directionLo := (149875333442500336067/100000000000000000000)
  directionHi := (37468833360625084017/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree010.table
  base := (4090335456939176660641747294760953137281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-7816959712930138627423872948839482000000000000)
      constant := (22746125534369508995775618502295969334364427693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree010.table
  base := (2032847337488084379865328999446436013801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-3912781215833014254090005215499428500000000000)
      constant := (11388555960256014909741154356903317029744939253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149875333442500336067/100000000000000000000)
  centralHi := (37468833360625084017/25000000000000000000)
  directionLo := (78991236459250935969/50000000000000000000)
  directionHi := (157982472918501871939/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree011.table
  base := (1842830772664255728797907623023953453727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (337896)
      previous := (168948)
      next := (168948)
      square := (6181444444406692499682787180700000000000000)
      linear := (-71029274826692174952145683357529500000000000)
      constant := (212688187095106703049944158648692710433340811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree011.table
  base := (1821397743135305325051352251535296520109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (337896)
      previous := (168948)
      next := (168948)
      square := (6181444444406692499682787180700000000000000)
      linear := (-71107481360654810231746933195342000000000000)
      constant := (213037174117370921121659210349737459068871537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78991236459250935969/50000000000000000000)
  centralHi := (157982472918501871939/100000000000000000000)
  directionLo := (82846707726363054179/50000000000000000000)
  directionHi := (165693415452726108359/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree012.table
  base := (-3888638115786902859002779191846484129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-9372124795129367710995382423682657000000000000)
      constant := (29347362118586152886933401661163070992239474815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree012.table
  base := (-19184468069111634992929916590779752971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-360863386831247521842413361625919500000000000)
      constant := (1130820295082642573907236832351588399610473749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82846707726363054179/50000000000000000000)
  centralHi := (165693415452726108359/100000000000000000000)
  directionLo := (43265282053956244873/25000000000000000000)
  directionHi := (173061128215824979493/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree013.table
  base := (-789314689906521087016714482774166547951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-390373359085730086645428352350163250000000000)
      constant := (1289836725219560871340477896973915248206452369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree013.table
  base := (-4985887829532211021908471966540565501/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 109202500000000000000000000000000000000000000
      center := (786258)
      previous := (393129)
      next := (393129)
      square := (14383745726407880624261870170475000000000000)
      linear := (-195401747511262290341617613229066000000000000)
      constant := (646194339283221605347356531448876402793065520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/25000000000000000000)
  centralHi := (173061128215824979493/100000000000000000000)
  directionLo := (22515966652258240663/12500000000000000000)
  directionHi := (36025546643613185061/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree014.table
  base := (-577919362581521605226235371629542792193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-10927289877328596794566891898525832000000000000)
      constant := (38269291313470928034688883404615358246624141855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree014.table
  base := (-2904667507803015077328365828934237593597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-10939333683558842627625484373548957000000000000)
      constant := (38348759209715378014504378862566566879763162759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22515966652258240663/12500000000000000000)
  centralHi := (36025546643613185061/20000000000000000000)
  directionLo := (93463691411723151997/50000000000000000000)
  directionHi := (37385476564689260799/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree015.table
  base := (-159649468949624819674017453204536600543/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-11704872418428211336352646635947419500000000000)
      constant := (43525886988041871667463783917710709991171395525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree015.table
  base := (-500590960452119866793006857032488372431/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-2929444124133011539371713214796620500000000000)
      constant := (10904812706752201042353118724299557713624878714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93463691411723151997/50000000000000000000)
  centralHi := (37385476564689260799/20000000000000000000)
  directionLo := (48372055869173943751/25000000000000000000)
  directionHi := (38697644695339155001/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree016.table
  base := (-4912565895114330274863674901884519201631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-12482454959527825878138401373369007000000000000)
      constant := (49289064612256807084344605161723957117796231757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree016.table
  base := (-196985436803060258569411715255374168409/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-12496219309505249687348221344824007000000000000)
      constant := (49397129062266297380800827444482812308661103075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48372055869173943751/25000000000000000000)
  centralHi := (38697644695339155001/20000000000000000000)
  directionLo := (99916888961666890711/50000000000000000000)
  directionHi := (199833777923333781423/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree017.table
  base := (-2838059767102520449126000844494899595107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-6630018750313720209962078055395297250000000000)
      constant := (27773013750557524400419585041037369741157204729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree017.table
  base := (-2843450976718242732890173201893132491033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-6637331061239226608604794915230766000000000000)
      constant := (27834805847113172459324900768945920566819437851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99916888961666890711/50000000000000000000)
  centralHi := (199833777923333781423/100000000000000000000)
  directionLo := (1287399646787699647/625000000000000000)
  directionHi := (205983943486031943521/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree018.table
  base := (-6299913214298094508259403552736701317811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-14037620041727054961709910848212182000000000000)
      constant := (62286545457279795423176392007609039759077070217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree018.table
  base := (-78869077693497823298346337986515083767/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-3513276233862914186767739579024764250000000000)
      constant := (15606619280924928669080423137028506752753154980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1287399646787699647/625000000000000000)
  centralHi := (205983943486031943521/100000000000000000000)
  directionLo := (2119557292195738673/1000000000000000000)
  directionHi := (211955729219573867301/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree019.table
  base := (-6798636185939364552020079362099838348709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (113256)
      previous := (56628)
      next := (56628)
      square := (2071896891338531281057111492700000000000000)
      linear := (-41039342334699915522148658131949500000000000)
      constant := (192527083506262662262550622459786751152480743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree019.table
  base := (-6807187862956287147514531608740055475063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (113256)
      previous := (56628)
      next := (56628)
      square := (2071896891338531281057111492700000000000000)
      linear := (-41084619801730914894549381722262000000000000)
      constant := (192962298469497466699999005325025205237725901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2119557292195738673/1000000000000000000)
  centralHi := (211955729219573867301/100000000000000000000)
  directionLo := (217763810868440298361/100000000000000000000)
  directionHi := (108881905434220149181/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree020.table
  base := (-7184421108398713629189652174263625739969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-15592785123926284045281420323055357000000000000)
      constant := (77186332999593756474850073663305329832681383443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree020.table
  base := (-1798002938101202786403529188247731996187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-3902497640349515951698423821843526750000000000)
      constant := (19340366107358187397855275370945292517769223489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217763810868440298361/100000000000000000000)
  centralHi := (108881905434220149181/50000000000000000000)
  directionLo := (223420955818585546461/100000000000000000000)
  directionHi := (111710477909292773231/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree021.table
  base := (-7467371781939257165206832034225794577763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-1259259051155838352851321158498226500000000000)
      constant := (6564075041960599287207895466030298551423734397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree021.table
  base := (-1494818963461257045222944363640300516657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-16388433374371267336655063773011632000000000000)
      constant := (85526967595564284679934551317751458216073862895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223420955818585546461/100000000000000000000)
  centralHi := (111710477909292773231/50000000000000000000)
  directionLo := (4578767068713361509/2000000000000000000)
  directionHi := (228938353435668075451/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree022.table
  base := (-3827972957842093398532194172176524619753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23465000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (3090722222203346249841393590350000000000000)
      linear := (-70859298372419475739061693379746000000000000)
      constant := (388171082842744595507013313263663351209499171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree022.table
  base := (-7661888232553168755719497316584070498819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (337896)
      previous := (168948)
      next := (168948)
      square := (6181444444406692499682787180700000000000000)
      linear := (-141875009812764222037325886435117000000000000)
      constant := (778108266288156884425450465259782457149042433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4578767068713361509/2000000000000000000)
  centralHi := (228938353435668075451/100000000000000000000)
  directionLo := (58581468832291256309/25000000000000000000)
  directionHi := (234325875329165025237/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree023.table
  base := (-7757245988221119335762355724706132445927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-17925532747225127670638684535320119500000000000)
      constant := (102995579343189546642857013258437926369058015269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree023.table
  base := (-3881244028545450390733529543670169661447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-8972659500158837198188900372143341000000000000)
      constant := (51614916393490250099438973649844810053488336709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58581468832291256309/25000000000000000000)
  centralHi := (234325875329165025237/100000000000000000000)
  directionLo := (119796141448424694203/50000000000000000000)
  directionHi := (239592282896849388407/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree024.table
  base := (-1944312044744003382083493315997767463443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-4675778822081185553106109818185426750000000000)
      constant := (28126028459952071342950737372012271127581502121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree024.table
  base := (-77818641317411018538919803114651627587/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-4680940453322719481559792307481051750000000000)
      constant := (28189943825471189133911791335742953982995982225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119796141448424694203/50000000000000000000)
  centralHi := (239592282896849388407/100000000000000000000)
  directionLo := (244745394642408799093/100000000000000000000)
  directionHi := (122372697321204399547/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree025.table
  base := (-1930246767706819758595903703128007944013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-4870174457356089188552548502540823625000000000)
      constant := (30615036658702288684774926998655807847937135911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree025.table
  base := (-3862522412920292821919066281455131786601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-750084793317849286773097604444682000000000000)
      constant := (4720695091960259014321440593130656044679481719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244745394642408799093/100000000000000000000)
  centralHi := (122372697321204399547/50000000000000000000)
  directionLo := (124896111202083613389/50000000000000000000)
  directionHi := (249792222404167226779/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree026.table
  base := (-1898176789512481025569041614616752348219/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 109202500000000000000000000000000000000000000
      center := (786258)
      previous := (393129)
      next := (393129)
      square := (14383745726407880624261870170475000000000000)
      linear := (-389582314817768678769152860530478500000000000)
      constant := (2555024374603550163190164290736901406302445861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree026.table
  base := (-7596268612478273684354141099218593313913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-1560049803018252691227838938553789000000000000)
      constant := (10243255171120574642284812041276446625454966247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124896111202083613389/50000000000000000000)
  centralHi := (249792222404167226779/100000000000000000000)
  directionLo := (254739083276511500391/100000000000000000000)
  directionHi := (31842385409563937549/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree027.table
  base := (-7395988465046187409711397860174595729671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-21035862911623585837781703485006469500000000000)
      constant := (143705443445937762172321607559350821712994133637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree027.table
  base := (-3699554876045157931288192067282068410741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-10529545126105244257911637343418391000000000000)
      constant := (72015240074087757722911207455254361513005490927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254739083276511500391/100000000000000000000)
  centralHi := (31842385409563937549/12500000000000000000)
  directionLo := (129795846161868734619/50000000000000000000)
  directionHi := (259591692323737469239/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree028.table
  base := (-7133851409343455146875521192560517933041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-21813445452723200379567458222428057000000000000)
      constant := (154990959381314436968143090175550978210168869027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree028.table
  base := (-57092665658625000632668454348643282289/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-21837533065183692045684643172474307000000000000)
      constant := (155340849106204376890884716780533291777793060375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129795846161868734619/50000000000000000000)
  centralHi := (259591692323737469239/100000000000000000000)
  directionLo := (33044404995978161963/12500000000000000000)
  directionHi := (52871047993565059141/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree029.table
  base := (-3404422355176466326941493657476473012803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-11295513996911407460676606479924822250000000000)
      constant := (83358183993775410843676489851548631643698278041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree029.table
  base := (-6811232587796456853115228369404455081089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-22615975878156895575546011658111832000000000000)
      constant := (167091979702309165449022715004851764031338368083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/12500000000000000000)
  centralHi := (52871047993565059141/20000000000000000000)
  directionLo := (53806891407473453627/20000000000000000000)
  directionHi := (33629307129670908517/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree030.table
  base := (-6423119278922662394248415421522126339099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-23368610534922429463138967697271232000000000000)
      constant := (178880447863469122872917109088722520054463615553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree030.table
  base := (-3212602030212831234260336889056549886249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-11697209345565049552703690071874678500000000000)
      constant := (89641326614579990176324373637272582227443846603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53806891407473453627/20000000000000000000)
  centralHi := (33629307129670908517/12500000000000000000)
  directionLo := (13681683490010972707/5000000000000000000)
  directionHi := (273633669800219454141/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree031.table
  base := (-747311303005542351457720566383451267251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-6036548269005511001231180608673204875000000000)
      constant := (47870542045103119964975701008431091731794185794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree031.table
  base := (-2990154282031084243755515329570875209851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-12086430752051651317634374314693441000000000000)
      constant := (95955920669850030869565766223823589705710480097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13681683490010972707/5000000000000000000)
  centralHi := (273633669800219454141/100000000000000000000)
  directionLo := (278156846802806653223/100000000000000000000)
  directionHi := (34769605850350831653/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree032.table
  base := (-5476490276065034706277305469190893460397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-24923775617121658546710477172114407000000000000)
      constant := (204520658913566916317524061386972517575833182359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree032.table
  base := (-2739037115132462059679169643231569679761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-12475652158538253082565058557512203500000000000)
      constant := (102489338139919632811569157319230785462638676867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278156846802806653223/100000000000000000000)
  centralHi := (34769605850350831653/12500000000000000000)
  directionLo := (282607638959431823067/100000000000000000000)
  directionHi := (70651909739857955767/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree033.table
  base := (-98368239841680773061622207913450209069/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23465000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (3090722222203346249841393590350000000000000)
      linear := (-106203959331492864002050545080727250000000000)
      constant := (900806552643777396407476508736855852658479575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree033.table
  base := (-1229947644630524398067468298431860253501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11732500000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (1545361111101673124920696795175000000000000)
      linear := (-53160634566218408460726209918723000000000000)
      constant := (451409970644767928123506010225381170455319807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282607638959431823067/100000000000000000000)
  centralHi := (70651909739857955767/25000000000000000000)
  directionLo := (286989414043739748069/100000000000000000000)
  directionHi := (28698941404373974807/10000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree034.table
  base := (-538168380714509316495373753051059849477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 109202500000000000000000000000000000000000000
      center := (786258)
      previous := (393129)
      next := (393129)
      square := (14383745726407880624261870170475000000000000)
      linear := (-509210398063863223659268973979953500000000000)
      constant := (4459714016587068824995990317931657075054990326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree034.table
  base := (-2153272895142700399959100765978835721493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-13254094971511456612426427043149728500000000000)
      constant := (116211235974641698775544832984700026699043035471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286989414043739748069/100000000000000000000)
  centralHi := (28698941404373974807/10000000000000000000)
  directionLo := (291305286509039521539/100000000000000000000)
  directionHi := (14565264325451976077/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree035.table
  base := (-909554172587226165322864706240716414249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-6814130810105125543016935346094792375000000000)
      constant := (61562491286316815557324522398567077004988212603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree035.table
  base := (-3639258152784945282058144403337554930399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-27286632755996116754714222571936982000000000000)
      constant := (246798293299327946112892191839922937232608136653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291305286509039521539/100000000000000000000)
  centralHi := (14565264325451976077/5000000000000000000)
  directionLo := (295558143388163339591/100000000000000000000)
  directionHi := (36944767923520417449/12500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree036.table
  base := (-729449627505436772311786997834081724017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-7008526445380029178463374030450189250000000000)
      constant := (65257313258645939458203894583594670565771774499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree036.table
  base := (-2918702588214544424089115266128045890751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-28065075568969320284575591057574507000000000000)
      constant := (261609449800308799384845273430139280256799372397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295558143388163339591/100000000000000000000)
  centralHi := (36944767923520417449/12500000000000000000)
  directionLo := (149875333442500336067/50000000000000000000)
  directionHi := (59950133377000134427/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree037.table
  base := (-2144748826832295432671815988808826418537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-28811688322619731255639250859222344500000000000)
      constant := (276242619836004924096939519682992667288629508939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree037.table
  base := (-1072766519164192177306111221121114429341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-14421759190971261907218479771606016000000000000)
      constant := (138427785054719508755632192788062885839205425127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149875333442500336067/50000000000000000000)
  centralHi := (59950133377000134427/20000000000000000000)
  directionLo := (75971338539999394089/25000000000000000000)
  directionHi := (303885354159997576357/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree038.table
  base := (-659810806247556576207184913596836633481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7865000000000000000000000000000000000000000
      center := (56628)
      previous := (28314)
      next := (28314)
      square := (1035948445669265640528555746350000000000000)
      linear := (-40982369617339814123857348471806000000000000)
      constant := (404279433483422065120133627767128457225534387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree038.table
  base := (-330075338231410667096675239359095644143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (2178)
      previous := (1089)
      next := (1089)
      square := (39844170987279447712636759475000000000000)
      linear := (-1577986426321954365240695079312250000000000)
      constant := (15583653359106892611199270849712424427058697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75971338539999394089/25000000000000000000)
  centralHi := (303885354159997576357/100000000000000000000)
  directionLo := (307964534724197867373/100000000000000000000)
  directionHi := (153982267362098933687/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree039.table
  base := (-221442224984197588239647266747617988367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-1167955900185344628431183089771750750000000000)
      constant := (11845014651279831489529012545883131040837641073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree039.table
  base := (-221736614382586531226035580552594059273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-1169246307995728110544603712095657000000000000)
      constant := (11871211446005919453650971966353924670146896087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307964534724197867373/100000000000000000000)
  centralHi := (153982267362098933687/50000000000000000000)
  directionLo := (62398077157180474053/20000000000000000000)
  directionHi := (155995192892951185133/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree040.table
  base := (485067994435094993674218330897216517619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-31144435945918574880996515071487107000000000000)
      constant := (324484285598289885537398954212567069591179502007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree040.table
  base := (484558340231764443970161355975810492763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-31178846820862134404021065000124607000000000000)
      constant := (325200817163659801338047072165088336915746947839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62398077157180474053/20000000000000000000)
  centralHi := (155995192892951185133/50000000000000000000)
  directionLo := (78991236459250935969/25000000000000000000)
  directionHi := (315964945837003743877/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree041.table
  base := (1463902600026826987269607539175808834597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-31922018487018189422782269808908694500000000000)
      constant := (341431275806491187409033780684357201246027410241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree041.table
  base := (1463461712766176131349652107982033933289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-31957289633835337933882433485762132000000000000)
      constant := (342184111236165717246181650803151572977619958517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78991236459250935969/25000000000000000000)
  centralHi := (315964945837003743877/100000000000000000000)
  directionLo := (319890126719667962989/100000000000000000000)
  directionHi := (31989012671966796299/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree042.table
  base := (623334548514041457667183134529177589267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-8174900257029450991142006136582570500000000000)
      constant := (89702797973272389505243366645190497534723033751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree042.table
  base := (2492957021991111568332005314911634123359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-32735732446808541463743801971399657000000000000)
      constant := (359601220890443012176033119332530360171851778227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319890126719667962989/100000000000000000000)
  centralHi := (31989012671966796299/10000000000000000000)
  directionLo := (16188386218804342649/5000000000000000000)
  directionHi := (323767724376086852981/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree043.table
  base := (3573137450766219942456390080738275019263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-33477183569217418506353779283751869500000000000)
      constant := (376623899091941969218036644492373167606388552339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree043.table
  base := (178640404634543790498554436602370184297/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-8378543814945436248401292614259295500000000000)
      constant := (94363003003421732026507245429916324534443021705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16188386218804342649/5000000000000000000)
  centralHi := (323767724376086852981/100000000000000000000)
  directionLo := (163799714226409948513/50000000000000000000)
  directionHi := (327599428452819897027/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree044.table
  base := (2351550026879142550359416426445986833831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23465000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (3090722222203346249841393590350000000000000)
      linear := (-141548620290566252265039396781708500000000000)
      constant := (1631691254763555651288003831676072516211168883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree044.table
  base := (2351407810168074622341949803360439367027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23465000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (3090722222203346249841393590350000000000000)
      linear := (-141705033358491522824241896457333500000000000)
      constant := (1635274262108357757466004111993575791949457711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163799714226409948513/50000000000000000000)
  centralHi := (327599428452819897027/100000000000000000000)
  directionLo := (82846707726363054179/25000000000000000000)
  directionHi := (331386830905452216717/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree045.table
  base := (367691057790451058444173474986931720421/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-8758087162854161897481322189648761125000000000)
      constant := (103386812390984203453954590555171157314663654452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree045.table
  base := (1470702853750879847238753168839321001271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-8767765221432038013331976857078058000000000000)
      constant := (103613550908224345057315868674668440964159741163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82846707726363054179/25000000000000000000)
  centralHi := (331386830905452216717/100000000000000000000)
  directionLo := (335131433727878319691/100000000000000000000)
  directionHi := (83782858431969579923/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree046.table
  base := (1778216337930138007201493367632264756901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-8952482798129065532927760874004158000000000000)
      constant := (108164428946534237585443182494069218454625503553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree046.table
  base := (7112653543911229487666344789492993893521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-35849503698701355583189275913949757000000000000)
      constant := (433605428024755417954836351638246049561417580413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335131433727878319691/100000000000000000000)
  centralHi := (83782858431969579923/25000000000000000000)
  directionLo := (67766931182531149327/20000000000000000000)
  directionHi := (84708663978163936659/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree047.table
  base := (4196202439124528150596257887131792896599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-1407212066677533718211415316670700750000000000)
      constant := (17392331304525608131891365422109965462703840919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree047.table
  base := (1678444446456059034228505146933850062527/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-36627946511674559113050644399587282000000000000)
      constant := (453189976591329119872218357918771149610280722655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67766931182531149327/20000000000000000000)
  centralHi := (84708663978163936659/25000000000000000000)
  directionLo := (42812229966738245267/12500000000000000000)
  directionHi := (342497839733905962137/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree048.table
  base := (9721573831985112961443694702601221992329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-37365096274715491215282552970859807000000000000)
      constant := (472175886223632571140507628119311772712009999637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree048.table
  base := (1944283280826686001776489742062888583639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-37406389324647762642912012885224807000000000000)
      constant := (473207791936321555949990148540224073354425785335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42812229966738245267/12500000000000000000)
  centralHi := (342497839733905962137/100000000000000000000)
  directionLo := (43265282053956244873/12500000000000000000)
  directionHi := (69224451286329991797/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree049.table
  base := (2775071598964948787774341915057703767709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-9535669703953776439267076927070348625000000000)
      constant := (123145870993139297038102702087614915488073608777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree049.table
  base := (11100150763127189423850748382110546103263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-38184832137620966172773381370862332000000000000)
      constant := (493658825623948212154748460191416326998876204339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/12500000000000000000)
  centralHi := (69224451286329991797/20000000000000000000)
  directionLo := (349709111365834117489/100000000000000000000)
  directionHi := (34970911136583411749/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree050.table
  base := (3132117533870620312362941240326001237241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-9730065339228680074713515611425745500000000000)
      constant := (128355841508088411201426169911721180233696013573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree050.table
  base := (2505670665821957310068756093144140417751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-38963274950594169702634749856499857000000000000)
      constant := (514543036780063955859442881354554372843205793015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349709111365834117489/100000000000000000000)
  centralHi := (34970911136583411749/10000000000000000000)
  directionLo := (176629774349644889417/50000000000000000000)
  directionHi := (70651909739857955767/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree051.table
  base := (1400606391220803040111778282180935835771/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-19848921949007167420319908591562284750000000000)
      constant := (267347748842629440965116986628762352621687848315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree051.table
  base := (14005963359258913162667004280066227474869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-3057055212582105633268932180164414000000000000)
      constant := (41220030070128839297783699232328125944829752789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176629774349644889417/50000000000000000000)
  centralHi := (70651909739857955767/20000000000000000000)
  directionLo := (178387327830601804641/50000000000000000000)
  directionHi := (356774655661203609283/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree052.table
  base := (15533016121645190581422561833993615136819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-3113494341470303798648120916965089000000000000)
      constant := (42799988432889577991540933226854515602791390739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree052.table
  base := (7766464796880447447692996706004298651389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-1558467714482329875475287954914419500000000000)
      constant := (21446571496567003952328809647945006519391322909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178387327830601804641/50000000000000000000)
  centralHi := (356774655661203609283/100000000000000000000)
  directionLo := (360255466436131850609/100000000000000000000)
  directionHi := (36025546643613185061/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree053.table
  base := (17109283206856195429386589634736984161697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-41253008980213563924211326657967744500000000000)
      constant := (578536397125332759243717856687702050964047126541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree053.table
  base := (17109208775365480005097363156959374921947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-41298603389513780292218855313412432000000000000)
      constant := (579794416213506204324278921618813311990052369791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360255466436131850609/100000000000000000000)
  centralHi := (36025546643613185061/10000000000000000000)
  directionLo := (45462870714748411621/12500000000000000000)
  directionHi := (363702965717987292969/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree054.table
  base := (9367414201705800327868278566534765136489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-21015295760656589232998540697694666000000000000)
      constant := (300552559650886032381647215543035099518300688117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree054.table
  base := (18734764400060242579288768637155872889943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-42077046202486983822080223799049957000000000000)
      constant := (602411042091054247470679829761122889388172802379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45462870714748411621/12500000000000000000)
  centralHi := (363702965717987292969/100000000000000000000)
  directionLo := (367118091963613198639/100000000000000000000)
  directionHi := (4588976149545164983/1250000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree055.table
  base := (510240517003608732717887487775385174031/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11732500000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (1545361111101673124920696795175000000000000)
      linear := (-88446640624819820264014124241344875000000000)
      constant := (1289475203586241991027966544217832869186024830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree055.table
  base := (10204782831391715433017807319821020721843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23465000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (3090722222203346249841393590350000000000000)
      linear := (-177088797584546228727031373077221000000000000)
      constant := (2584548425829088848273413793834860206497609199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367118091963613198639/100000000000000000000)
  centralHi := (4588976149545164983/1250000000000000000)
  directionLo := (370501740376409670057/100000000000000000000)
  directionHi := (185250870188204835029/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree056.table
  base := (22133633845085302740892580903198398206433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-43585756603512407549568590870232507000000000000)
      constant := (647539019954051684638082443195123299516717598349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree056.table
  base := (5533396641931723143644317949257307406657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-10908482957108347720450740192581251750000000000)
      constant := (162235858082616079763993137747848351532792397421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370501740376409670057/100000000000000000000)
  centralHi := (185250870188204835029/50000000000000000000)
  directionLo := (93463691411723151997/25000000000000000000)
  directionHi := (373854765646892607989/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree057.table
  base := (11953422895410739186780958632227321415183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7865000000000000000000000000000000000000000
      center := (56628)
      previous := (28314)
      next := (28314)
      square := (1035948445669265640528555746350000000000000)
      linear := (-61445068067329670486640367877637250000000000)
      constant := (929922674519311583530011725892587725023582859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree057.table
  base := (23906805177534144576969918558929197313837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (113256)
      previous := (56628)
      next := (56628)
      square := (2071896891338531281057111492700000000000000)
      linear := (-123025968535752339090482906526212000000000000)
      constant := (1863875815715609445369658685629756189874665601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93463691411723151997/25000000000000000000)
  centralHi := (373854765646892607989/100000000000000000000)
  directionLo := (377177984473958276963/100000000000000000000)
  directionHi := (94294496118489569241/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree058.table
  base := (12864618928767554680560100628315381265741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-22570460842855818316570050172537841000000000000)
      constant := (347850720543190730656358750608756906104144824073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree058.table
  base := (25729202979710008177056296701553055134481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-45190817454379797941525697741600057000000000000)
      constant := (697207919966875648741439854116728713017280439293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377177984473958276963/100000000000000000000)
  centralHi := (94294496118489569241/25000000000000000000)
  directionLo := (1521888711551706221/400000000000000000)
  directionHi := (380472177887926555251/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree059.table
  base := (13800397147686057649137915442997998999863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-22959252113405625587462927541248634750000000000)
      constant := (360215410630382644764921748248686865437006704139) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree059.table
  base := (6900191087985838429672313751610445921947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-11492315066838250367846766556809395500000000000)
      constant := (180497418734977498509079907135924495501240369791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1521888711551706221/400000000000000000)
  centralHi := (380472177887926555251/100000000000000000000)
  directionLo := (383738093394083755133/100000000000000000000)
  directionHi := (191869046697041877567/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree060.table
  base := (3690187726331291213581170231193348514399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 109202500000000000000000000000000000000000000
      center := (786258)
      previous := (393129)
      next := (393129)
      square := (14383745726407880624261870170475000000000000)
      linear := (-898001668613670494552146342690747250000000000)
      constant := (14338313538023791320767979910542973312914925438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree060.table
  base := (29521476110901153987583098194108934072631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-46747703080326205001248434712875107000000000000)
      constant := (747204426906242836160372333871707573039945731243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383738093394083755133/100000000000000000000)
  centralHi := (191869046697041877567/50000000000000000000)
  directionLo := (386976446953391550009/100000000000000000000)
  directionHi := (38697644695339155001/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree061.table
  base := (31491349182833318645916495772598483137529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-47473669309010480258497364557340444500000000000)
      constant := (771185882864181763137269785965136653991970255237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree061.table
  base := (15745663565731368077690093296451599856043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-23763072946649704265554901599256316000000000000)
      constant := (386426084774220512842998299670145638364303585679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386976446953391550009/100000000000000000000)
  centralHi := (38697644695339155001/10000000000000000000)
  directionLo := (39018792481523000353/10000000000000000000)
  directionHi := (390187924815230003531/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree062.table
  base := (33510326941234437309644186210541783281977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-48251251850110094800283119294762032000000000000)
      constant := (797211552543641309591987681625369131324520485381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree062.table
  base := (16755154012698734322362443003945163139677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-24152294353136306030485585842075078500000000000)
      constant := (399466448767684816890048148002476545974355003481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39018792481523000353/10000000000000000000)
  centralHi := (390187924815230003531/100000000000000000000)
  directionLo := (49171648151933056373/12500000000000000000)
  directionHi := (78674637043092890197/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree063.table
  base := (35578427092136647738297327839734316233271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-49028834391209709342068874032183619500000000000)
      constant := (823669308476359586886517048165585752222886637163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree063.table
  base := (1778920543510293748387321287757279183799/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-12270757879811453897708135042446920500000000000)
      constant := (206361651592053391305151135780128577234914067735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49171648151933056373/12500000000000000000)
  centralHi := (78674637043092890197/20000000000000000000)
  directionLo := (99133214987934485889/25000000000000000000)
  directionHi := (396532859951737943557/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree064.table
  base := (2355977680529133750465586131794745558619/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-12451604233077330970963657192401301750000000000)
      constant := (212639786707747622708460625029578053598793900028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree064.table
  base := (37695628980292911842980169349826287522359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-3835498025555309163130300665801939000000000000)
      constant := (65568714788502893684231677112703658065264163479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99133214987934485889/25000000000000000000)
  centralHi := (396532859951737943557/100000000000000000000)
  directionLo := (79933511169333512569/20000000000000000000)
  directionHi := (199833777923333781423/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree065.table
  base := (39861968635383809997567971944424634698237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-3891076882569918340433875654386676500000000000)
      constant := (67529312644130965510951940413824234577628690397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree065.table
  base := (39861956713864724016329779747311054308417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-3895378241937863280811944395466364000000000000)
      constant := (67674842459894786593516438981465649475745962977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79933511169333512569/20000000000000000000)
  centralHi := (199833777923333781423/50000000000000000000)
  directionLo := (100694464027135589637/25000000000000000000)
  directionHi := (402777856108542358549/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree066.table
  base := (1314918735193545965591278838470482883719/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 11732500000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (1545361111101673124920696795175000000000000)
      linear := (-106118971104356514395508550091835500000000000)
      constant := (1871146814824377932941422257521146387511346136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree066.table
  base := (21038694654985950807166625698311477584803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 23465000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (3090722222203346249841393590350000000000000)
      linear := (-212472561810600934629820849697108500000000000)
      constant := (3750353648136272658834029899851624264305480479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100694464027135589637/25000000000000000000)
  centralHi := (402777856108542358549/100000000000000000000)
  directionLo := (405864321598164342357/100000000000000000000)
  directionHi := (202932160799082171179/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree067.table
  base := (44341931503839127177702124209557150284441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-52139164555608167509211892981869969500000000000)
      constant := (933821126531068176305803542871994701632345675173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree067.table
  base := (44341922750992913805232300769012472198927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-52196802771138629710278014112337782000000000000)
      constant := (935831182580156451913969952903615441188077293731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405864321598164342357/100000000000000000000)
  centralHi := (202932160799082171179/50000000000000000000)
  directionLo := (408927492009625941717/100000000000000000000)
  directionHi := (204463746004812970859/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree068.table
  base := (46655561144000883476321406968402801295237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-52916747096707782050997647719291557000000000000)
      constant := (962439266897399996390347085774506699423904216161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree068.table
  base := (46655553646586119673470336235349236205799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-52975245584111833240139382597975307000000000000)
      constant := (964509749246951959325296300951243983327171579547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408927492009625941717/100000000000000000000)
  centralHi := (204463746004812970859/50000000000000000000)
  directionLo := (1287399646787699647/312500000000000000)
  directionHi := (411967886972063887041/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree069.table
  base := (49018285556421337365898613803848890190247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-53694329637807396592783402456713144500000000000)
      constant := (991489477832753043055832117382368178638077329691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree069.table
  base := (12254569783939695681533900290477299322223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-13438422099271259192500187770903208000000000000)
      constant := (248405320306185299319026215041812148867647297219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1287399646787699647/312500000000000000)
  centralHi := (411967886972063887041/100000000000000000000)
  directionLo := (414986007078758890391/100000000000000000000)
  directionHi := (51873250884844861299/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree070.table
  base := (51430102301619542231751474976325125804717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-54471912178907011134569157194134732000000000000)
      constant := (1020971757951860742324271466777154930726085962601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree070.table
  base := (25715048402112372962113347215465114445179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-27266065605029120149931059784625178500000000000)
      constant := (511582888571282264316663783961352350383038230687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414986007078758890391/100000000000000000000)
  centralHi := (51873250884844861299/12500000000000000000)
  directionLo := (417982334849352505051/100000000000000000000)
  directionHi := (104495583712338126263/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree071.table
  base := (13472752330148239328784646148912531773291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-13812373680001656419088727982889079875000000000)
      constant := (262721526521378081104547887599977446979277364223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree071.table
  base := (6736375576832996334062634456129401181011/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-13827643505757860957430872013721970500000000000)
      constant := (263285808960880914380135040481902980150806278766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417982334849352505051/100000000000000000000)
  centralHi := (104495583712338126263/25000000000000000000)
  directionLo := (420957335630418441291/100000000000000000000)
  directionHi := (105239333907604610323/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree072.table
  base := (2820050243774099936752769657815702656579/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-14006769315276560054535166667244476750000000000)
      constant := (270308130311714752763003072950070117628231774435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree072.table
  base := (14100250211967439463453013013045548778919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-14022254209001161839896214135131351750000000000)
      constant := (270888414087840475555993385313957686260755490907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420957335630418441291/100000000000000000000)
  centralHi := (105239333907604610323/25000000000000000000)
  directionLo := (2119557292195738673/500000000000000000)
  directionHi := (423911458439147734601/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree073.table
  base := (29480043749743824527943178812027338415583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-2184794607777148259997170054092288250000000000)
      constant := (42769653946268253068379503769985848849018581023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree073.table
  base := (58960084053083913024639915506694427030487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-56867459648977850889446225026162932000000000000)
      constant := (1114397037842261869754291709084528425535043134411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2119557292195738673/500000000000000000)
  centralHi := (423911458439147734601/100000000000000000000)
  directionLo := (426845136754478901061/100000000000000000000)
  directionHi := (213422568377239450531/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree074.table
  base := (30784127977299586671318425983828650677507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-28791121171652734650856088071910541000000000000)
      constant := (571610774725425460365357232841130613679424382471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree074.table
  base := (61568253006085472576780213663055628533671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-57645902461951054419307593511800457000000000000)
      constant := (1145673379621046013263684942533675095829730678363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426845136754478901061/100000000000000000000)
  centralHi := (213422568377239450531/50000000000000000000)
  directionLo := (42975878925961981141/10000000000000000000)
  directionHi := (429758789259619811411/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree075.table
  base := (2569020367836560292986583294061657498747/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-58359824884405083843497930881242669500000000000)
      constant := (1174864161197136978081777356306752054812774504775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree075.table
  base := (32112753336911268288143793151684555637077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-29212172637462128974584480998718991000000000000)
      constant := (588691340550546356109481283483728733878431085681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42975878925961981141/10000000000000000000)
  centralHi := (429758789259619811411/100000000000000000000)
  directionLo := (43265282053956244873/10000000000000000000)
  directionHi := (432652820539562448731/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree076.table
  base := (13386369268304362240509718083272173522501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (113256)
      previous := (56628)
      next := (56628)
      square := (2071896891338531281057111492700000000000000)
      linear := (-163815533034639053698846774566937000000000000)
      constant := (3343320879061045206772673629988572644754470365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree076.table
  base := (66931844184565724282933090717892920522171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (113256)
      previous := (56628)
      next := (56628)
      square := (2071896891338531281057111492700000000000000)
      linear := (-163996642902763051188449668928187000000000000)
      constant := (3350484603289162943431145032081220063981374983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/10000000000000000000)
  centralHi := (432652820539562448731/100000000000000000000)
  directionLo := (435527621736880596723/100000000000000000000)
  directionHi := (108881905434220149181/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree077.table
  base := (69687266647084992751528355821005576932803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (337896)
      previous := (168948)
      next := (168948)
      square := (6181444444406692499682787180700000000000000)
      linear := (-495165206335572834108011903769304500000000000)
      constant := (10243351879833699261674223159358420594420644479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree077.table
  base := (13937452960544247516288752280393154288887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (25992)
      previous := (12996)
      next := (12996)
      square := (475495726492822499975599013900000000000000)
      linear := (-38131742467177790851170819433384000000000000)
      constant := (789637737611075778322679727968560455991441035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435527621736880596723/100000000000000000000)
  centralHi := (108881905434220149181/25000000000000000000)
  directionLo := (438383571168819995259/100000000000000000000)
  directionHi := (21919178558440999763/5000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree078.table
  base := (36245884742191657179855605499225717128139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-2334329711834766441109815195904132000000000000)
      constant := (48937860815266196328695720573857584706124239659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree078.table
  base := (72491767907576091267050302038306893805591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-4673821054911066810673312881103889000000000000)
      constant := (98085256859470931661559559560421237928322020471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438383571168819995259/100000000000000000000)
  centralHi := (21919178558440999763/5000000000000000000)
  directionLo := (55152629363554653581/12500000000000000000)
  directionHi := (441221034908437228649/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree079.table
  base := (1883633858080110222697067094647582123237/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-15367538762200885502660237457732254875000000000)
      constant := (326438812062771279497427770669649984775983751610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree079.table
  base := (37672676487680816938569370272203264276179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-30769058263408536034307217969994041000000000000)
      constant := (654274737611331979717870405632571258135271073687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55152629363554653581/12500000000000000000)
  centralHi := (441221034908437228649/100000000000000000000)
  directionLo := (444040367332314620563/100000000000000000000)
  directionHi := (111010091833078655141/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree080.table
  base := (19562005179014607360295821596373674386567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-15561934397475789138106676142087651750000000000)
      constant := (334889544592065299732647555208198813871435230651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree080.table
  base := (39124009782058659177650310623291162885647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-31158279669895137799237902212812803500000000000)
      constant := (671211784579939560140176056126938661718103305891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444040367332314620563/100000000000000000000)
  centralHi := (111010091833078655141/25000000000000000000)
  directionLo := (223420955818585546461/50000000000000000000)
  directionHi := (446841911637171092923/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree081.table
  base := (40599884142638212383171997118291401060721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-31512660065501385547106229652886097250000000000)
      constant := (686896585666994450213387376989524207927471102013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree081.table
  base := (81199767300917556055490046977844045971019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-63095002152763479128337172911263132000000000000)
      constant := (1376730620773000679844685076407713606099281052207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223420955818585546461/50000000000000000000)
  centralHi := (446841911637171092923/100000000000000000000)
  directionLo := (449626000327501008201/100000000000000000000)
  directionHi := (224813000163750504101/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree082.table
  base := (42100298356060355844440672220850419328197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-31901451336051192817999107021596891000000000000)
      constant := (704230113483636036431613832130322114073024651041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree082.table
  base := (42100297935546368066520483692586129839771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-31936722482868341329099270698450328500000000000)
      constant := (705735314941671277800881776517769111087903481663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449626000327501008201/100000000000000000000)
  centralHi := (224813000163750504101/50000000000000000000)
  directionLo := (113098238919050606959/25000000000000000000)
  directionHi := (452392955676202427837/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree083.table
  base := (17450101145518696654333275404944491736641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-64580485213202000177783968780615369500000000000)
      constant := (1443559345115359504577279460368259417002509008865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree083.table
  base := (43625252504566543140676669530634722035907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-32325943889354943094029954941269091000000000000)
      constant := (723321798170067113408983893844193525718505897671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113098238919050606959/25000000000000000000)
  centralHi := (452392955676202427837/100000000000000000000)
  directionLo := (455143090160001190157/100000000000000000000)
  directionHi := (227571545080000595079/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree084.table
  base := (45174747552339410688891316693458773354027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-32679033877150807359784861759018478500000000000)
      constant := (739545262824669762703563860268614645075404294031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree084.table
  base := (18069898898202530680601078378550633908237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-65430330591683089717921278368175707000000000000)
      constant := (1482249520016161883949067535942065541083470525805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455143090160001190157/100000000000000000000)
  centralHi := (227571545080000595079/50000000000000000000)
  directionLo := (457876706871336150901/100000000000000000000)
  directionHi := (228938353435668075451/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree085.table
  base := (46748782325897290270746626355389153232059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-33067825147700614630677739127729272250000000000)
      constant := (757526884230210819651808685570874796478721899327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree085.table
  base := (1869951282554233956486739584155569577169/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-33104386702328146623891323426906616000000000000)
      constant := (759144200402045050381077931264263258308853703925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457876706871336150901/100000000000000000000)
  centralHi := (228938353435668075451/50000000000000000000)
  directionLo := (92118819981648485657/20000000000000000000)
  directionHi := (230297049954121214143/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree086.table
  base := (24173678551816367186781735029998858681027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 109202500000000000000000000000000000000000000
      center := (786258)
      previous := (393129)
      next := (393129)
      square := (14383745726407880624261870170475000000000000)
      linear := (-1286792939163477765445023711401541000000000000)
      constant := (29835559104938423974418719622546604974170940387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree086.table
  base := (96694713759750406611811674914826924327323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-66987216217629496777644015339450757000000000000)
      constant := (1554760238613357787043485307282422952960043347519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92118819981648485657/20000000000000000000)
  centralHi := (230297049954121214143/50000000000000000000)
  directionLo := (57911944342956537533/12500000000000000000)
  directionHi := (92659110948730460053/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree087.table
  base := (99940943634658073293817948766323999649733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-67690815377600458344926987730301719500000000000)
      constant := (1588276440560994624803171151284234457969974833249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree087.table
  base := (1249261790657200500518673560065504393243/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-16941414757650675076876345956272070500000000000)
      constant := (397916258341889691470649967806396422777449345580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57911944342956537533/12500000000000000000)
  centralHi := (92659110948730460053/20000000000000000000)
  directionLo := (232990674287713199857/50000000000000000000)
  directionHi := (93196269715085279943/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree088.table
  base := (12904531602355426784692472328116182420617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11732500000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (1545361111101673124920696795175000000000000)
      linear := (-141463632063429902658497401792816750000000000)
      constant := (3358545185346353382393325214377231863199911162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree088.table
  base := (103236252492670273870015044080915946561491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46930000000000000000000000000000000000000000
      center := (337896)
      previous := (168948)
      next := (168948)
      square := (6181444444406692499682787180700000000000000)
      linear := (-566480180525420692870799605873767000000000000)
      constant := (13462832933902738151263884171336509537213077263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232990674287713199857/50000000000000000000)
  centralHi := (93196269715085279943/20000000000000000000)
  directionLo := (58581468832291256309/12500000000000000000)
  directionHi := (468651750658330050473/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree089.table
  base := (106580641662673569832864892109884652862837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-69245980459799687428498497205144894500000000000)
      constant := (1663227360841553544620319554294679253953995578961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree089.table
  base := (106580641384264300624529551285143933771817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-69322544656549107367228120796363332000000000000)
      constant := (1666773493462992833674597854476821825286627598901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58581468832291256309/12500000000000000000)
  centralHi := (468651750658330050473/100000000000000000000)
  directionLo := (94261404523816019497/20000000000000000000)
  directionHi := (235653511309540048743/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree090.table
  base := (54987055042088305035245880094432297025733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2839265000000000000000000000000000000000000000
      center := (20442708)
      previous := (10221354)
      next := (10221354)
      square := (373977388886604896230808624432350000000000000)
      linear := (-35011781500449650985142125971283241000000000000)
      constant := (850675456958101070562796030863469357069203561249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree090.table
  base := (54987054923283403202678216461765798333841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (1572516)
      previous := (786258)
      next := (786258)
      square := (28767491452815761248523740340950000000000000)
      linear := (-2696191825750858111426518818538494500000000000)
      constant := (65576044565537143385604920793045646837020508721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94261404523816019497/20000000000000000000)
  centralHi := (235653511309540048743/50000000000000000000)
  directionLo := (94789483751101123163/20000000000000000000)
  directionHi := (59243427344438201977/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree091.table
  base := (113416658014189010370497611431354192652011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-5446241964769147424005385129229851500000000000)
      constant := (133838963760946623972937686194632793598607492491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree091.table
  base := (22683331562284950525928948125697198733997/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3145032)
      previous := (1572516)
      next := (1572516)
      square := (57534982905631522497047480681900000000000000)
      linear := (-5452263867884270340534681366741414000000000000)
      constant := (134124136975880699379840967967340759751998614785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94789483751101123163/20000000000000000000)
  centralHi := (59243427344438201977/12500000000000000000)
  directionLo := (476573186320790727413/100000000000000000000)
  directionHi := (238286593160395363707/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree092.table
  base := (29227071348589329900495032917995404243399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-17894682020774632763463940354352414250000000000)
      constant := (444723551434182318475769214724698292785826852347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree092.table
  base := (3653383913167168517070465137708163878479/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-17914468273867179489203056563318976750000000000)
      constant := (445670839844449442025584228437264890988087484696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476573186320790727413/100000000000000000000)
  centralHi := (238286593160395363707/50000000000000000000)
  directionLo := (119796141448424694203/25000000000000000000)
  directionHi := (479184565793698776813/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree093.table
  base := (120448992175451498098538386871988609453407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-72356310624198145595641516154831244500000000000)
      constant := (1818313944421516202175568107235928284390820525171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree093.table
  base := (752806200174065632766168912885005662279/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-18109078977110480371668398684728358000000000000)
      constant := (455546473687619109207911593805175874829309679480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119796141448424694203/25000000000000000000)
  centralHi := (479184565793698776813/100000000000000000000)
  directionLo := (96356358227122749553/20000000000000000000)
  directionHi := (240890895567806873883/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree094.table
  base := (24807755663188264070997368596260213935719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-73133893165297760137427270892252832000000000000)
      constant := (1858165744923083833321867544474694928382699206535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree094.table
  base := (124038778190030699903965609308158484602267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-73214758721415125016534963224550957000000000000)
      constant := (1862121386781261398873811009327172390456851122751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96356358227122749553/20000000000000000000)
  centralHi := (240890895567806873883/50000000000000000000)
  directionLo := (121091272508794132779/25000000000000000000)
  directionHi := (484365090035176531117/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree095.table
  base := (127677643780794817152000834482540088537417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15730000000000000000000000000000000000000000
      center := (113256)
      previous := (56628)
      next := (56628)
      square := (2071896891338531281057111492700000000000000)
      linear := (-204740929934618766424412813378599500000000000)
      constant := (5258863177899000439127074795919814231144356941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree095.table
  base := (63838821836699633686996413293292133403353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7865000000000000000000000000000000000000000
      center := (56628)
      previous := (28314)
      next := (28314)
      square := (1035948445669265640528555746350000000000000)
      linear := (-102483658634886881643208215665081000000000000)
      constant := (2635027472923222984415521955474016182093474269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121091272508794132779/25000000000000000000)
  centralHi := (484365090035176531117/100000000000000000000)
  directionLo := (19477387365649600801/4000000000000000000)
  directionHi := (243467342070620010013/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree096.table
  base := (131365588540464129543562774393039075768437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-74689058247496989220998780367096007000000000000)
      constant := (1939165531300103337438514552972134140292334255761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree096.table
  base := (6568279422443558578083515480211169570313/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-18692911086840383019064425048956501750000000000)
      constant := (485822810185469300431566051591454109370054739945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19477387365649600801/4000000000000000000)
  centralHi := (243467342070620010013/50000000000000000000)
  directionLo := (244745394642408799093/50000000000000000000)
  directionHi := (489490789284817598187/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree097.table
  base := (33775653142507386795918843269444735811037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1419632500000000000000000000000000000000000000
      center := (10221354)
      previous := (5110677)
      next := (5110677)
      square := (186988694443302448115404312216175000000000000)
      linear := (-18866660197149150940696133776129398625000000000)
      constant := (495078379286156409445920900124706010669973543561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree097.table
  base := (135102612491922403038750459684484662368707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-75550087160334735606119068681463532000000000000)
      constant := (1984525602641265987482724389216604312042557376071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell113.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244745394642408799093/50000000000000000000)
  centralHi := (489490789284817598187/100000000000000000000)
  directionLo := (98406723138130805363/20000000000000000000)
  directionHi := (7688025245166469169/1562500000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree098.table
  base := (138888715848477061406048625163477599730453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-76244223329696218304570289841939182000000000000)
      constant := (2021893564743173191697202365485888289252236927409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree098.table
  base := (138888715781877207776202474103350858818471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5678530000000000000000000000000000000000000000
      center := (40885416)
      previous := (20442708)
      next := (20442708)
      square := (747954777773209792461617248864700000000000000)
      linear := (-76328529973307939135980437167101057000000000000)
      constant := (2026192921136992563064740171985361956232645212763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell113.Kernel098
