import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell192.Parameters
import ForestUnimodality.BinomialMassData.Q6_11.Batch000_049
import ForestUnimodality.BinomialMassData.Q6_11.Batch050_099
import ForestUnimodality.BinomialMassData.Q97_177.Batch000_049
import ForestUnimodality.BinomialMassData.Q97_177.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree000.table
  base := (111791203710876642056746277/4000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (378)
      previous := (0)
      next := (315)
      square := (16586446583366052653918387400000000000000)
      linear := (-59156551367526946094699269200000000000000)
      constant := (3074258102049107656560522617500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree000.table
  base := (111791203710876642056746277/4000000000000000000000000)
  polynomial :=
    { denominator := 590000000000000000000000000000000000000000
      center := (2037)
      previous := (0)
      next := (1680)
      square := (88963668038054282416471350600000000000000)
      linear := (-317294230062189983598841534800000000000000)
      constant := (16489202547354304703370075857500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree001.table
  base := (35308974660347996731260687737013651756129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-849759424043189038888712610000000000000000)
      constant := (21771151893806715871302826418493259312458045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree001.table
  base := (176067000632575500256949594451529481174071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-73420030320390157885790393676000000000000000)
      constant := (1874174375676651443938494610613122371900823453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49768848690497718649/100000000000000000000)
  directionHi := (995376973809954373/2000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree002.table
  base := (113357967588754934630413601571064413757063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-1048796783043581670735733258800000000000000)
      constant := (14643324359013735132704095910098794064604623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree002.table
  base := (112776796738111722479465807562026051497187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-90678981919772688674585835692400000000000000)
      constant := (1258199759986697840055566153642238055785123841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768848690497718649/100000000000000000000)
  centralHi := (995376973809954373/2000000000000000000)
  directionLo := (2815351232071853011/4000000000000000000)
  directionHi := (17595945200449081319/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree003.table
  base := (74005719418675822349902260241560759757929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-1247834142043974302582753907600000000000000)
      constant := (10508056219094405084939992836428851930709409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree003.table
  base := (36734973106566751965390143875421033150613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-35979311173051739821127092569600000000000000)
      constant := (300713866347849354630380911176881232794567706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815351232071853011/4000000000000000000)
  centralHi := (17595945200449081319/25000000000000000000)
  directionLo := (86202174566149834763/100000000000000000000)
  directionHi := (21550543641537458691/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree004.table
  base := (6128125814403331275283249460943191383991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-1446871501044366934429774556400000000000000)
      constant := (8220309678619330137897603497393009259703288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree004.table
  base := (24289942236564999863640470032238458155057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-125196885118537750252176719725200000000000000)
      constant := (706096258891155362325663242678932437026520502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86202174566149834763/100000000000000000000)
  centralHi := (21550543641537458691/25000000000000000000)
  directionLo := (49768848690497718649/50000000000000000000)
  directionHi := (99537697380995437299/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree005.table
  base := (6555380934039834039666445898086445602489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-1645908860044759566276795205200000000000000)
      constant := (7097774908395312284887045904342299589505845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree005.table
  base := (16212080799372123768685150252519724892977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-142455836717920281040972161741600000000000000)
      constant := (610721915021674977730255364557126974114717622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49768848690497718649/50000000000000000000)
  centralHi := (99537697380995437299/100000000000000000000)
  directionLo := (111286528833854290641/100000000000000000000)
  directionHi := (55643264416927145321/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree006.table
  base := (21893090281620850925524561056145977305671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-1844946219045152198123815854000000000000000)
      constant := (6732884752583675224986575585393663253986191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree006.table
  base := (21619037118355726280819322926632564222157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-53238262772434270609922534586000000000000000)
      constant := (193560721896657936154695723421207956057328517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111286528833854290641/100000000000000000000)
  centralHi := (55643264416927145321/50000000000000000000)
  directionLo := (121908284377502166973/100000000000000000000)
  directionHi := (60954142188751083487/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree007.table
  base := (114816231266901963641086026190520791801/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-2043983578045544829970836502800000000000000)
      constant := (6881033543807816379822616850131626975990125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree007.table
  base := (14139891455271814726180639687441510733933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-176973739916685342618563045774400000000000000)
      constant := (594833908656650811007153799514951696594462319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121908284377502166973/100000000000000000000)
  centralHi := (60954142188751083487/50000000000000000000)
  directionLo := (32918999168264892921/25000000000000000000)
  directionHi := (26335199334611914337/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree008.table
  base := (558348663848121356762044804090640959753/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-2243020937045937461817857151600000000000000)
      constant := (7394584108676291387839425895919480898081808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree008.table
  base := (4384139629883858096155150529059202931991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-194232691516067873407358487790800000000000000)
      constant := (640452919134529933618268985287530512437564026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32918999168264892921/25000000000000000000)
  centralHi := (26335199334611914337/20000000000000000000)
  directionLo := (2815351232071853011/2000000000000000000)
  directionHi := (140767561603592650551/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree009.table
  base := (4895663788741775269087133859566274026369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-2442058296046330093664877800400000000000000)
      constant := (8183745295656519854748396248207519157190649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree009.table
  base := (4765182188574552714096896325142225043441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-70497214371816801398717976602400000000000000)
      constant := (236607209521618094569258088500020085376218121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815351232071853011/2000000000000000000)
  centralHi := (140767561603592650551/100000000000000000000)
  directionLo := (37326636517873288987/25000000000000000000)
  directionHi := (149306546071493155949/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree010.table
  base := (222800216853529989535219996595800204683/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-2641095655046722725511898449200000000000000)
      constant := (9193355301067451027743521348704734598133144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree010.table
  base := (335544787988445997107010871029803150443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-228750594714832934984949371823600000000000000)
      constant := (798210649728447626438055549406821171500381245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37326636517873288987/25000000000000000000)
  centralHi := (149306546071493155949/100000000000000000000)
  directionLo := (78691459193130617731/50000000000000000000)
  directionHi := (157382918386261235463/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree011.table
  base := (-689938412019712601542757656100716240869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (378)
      previous := (0)
      next := (315)
      square := (16586446583366052653918387400000000000000)
      linear := (-258193910367919577941719918000000000000000)
      constant := (944462062674122733492287227382892121350441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree011.table
  base := (-155069604552036846275419013904120379143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-246009546314215465773744813840000000000000000)
      constant := (902682862385273136447659306324796354403048255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78691459193130617731/50000000000000000000)
  centralHi := (157382918386261235463/100000000000000000000)
  directionLo := (82532298677175806213/50000000000000000000)
  directionHi := (165064597354351612427/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree012.table
  base := (-16880396751468617317239014982869478247/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-3039170373047507989205939746800000000000000)
      constant := (11749207134459836501912320077931646901138080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree012.table
  base := (-2771663537365840336556780168614504576541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-87756165971199332187513418618800000000000000)
      constant := (340461092712946408036749973985052909569060779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82532298677175806213/50000000000000000000)
  centralHi := (165064597354351612427/100000000000000000000)
  directionLo := (86202174566149834763/50000000000000000000)
  directionHi := (172404349132299669527/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree013.table
  base := (-2183118590751074336507942323383583884301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-3238207732047900621052960395600000000000000)
      constant := (13259709127087074928355209040941172699999158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree013.table
  base := (-2212866172680241090024401297127720209139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-280527449512980527351335697872800000000000000)
      constant := (1153116071758810266399809532644790435711922846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86202174566149834763/50000000000000000000)
  centralHi := (172404349132299669527/100000000000000000000)
  directionLo := (1401907311518737053/781250000000000000)
  directionHi := (35888827174879668557/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree014.table
  base := (-360163869774322444782631031664653449323/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-3437245091048293252899981044400000000000000)
      constant := (14911324616828344993950850525897230922110672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree014.table
  base := (-1453292222866890775714482941973663581573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-297786401112363058140131139889200000000000000)
      constant := (1297091601598939240076225331325476124870532644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1401907311518737053/781250000000000000)
  centralHi := (35888827174879668557/20000000000000000000)
  directionLo := (37243596066807077743/20000000000000000000)
  directionHi := (46554495083508847179/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree015.table
  base := (-6941959816229320296756333232300395247791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-3636282450048685884747001693200000000000000)
      constant := (16697768605792316165046230446891652175017289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree015.table
  base := (-1397052650086915786154717017578308876743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-105015117570581862976308860635200000000000000)
      constant := (484258081802879348743592810702049534000288085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37243596066807077743/20000000000000000000)
  centralHi := (46554495083508847179/25000000000000000000)
  directionLo := (96376961069107236177/50000000000000000000)
  directionHi := (38550784427642894471/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree016.table
  base := (-3970246059741124776661166883725766682597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-3835319809049078516594022342000000000000000)
      constant := (18614655904125374743549296391738364462811526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree016.table
  base := (-1595562359509699421573892813636969250499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-332304304311128119717722023922000000000000000)
      constant := (1619790181640784883845007170076745650585194715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96376961069107236177/50000000000000000000)
  centralHi := (38550784427642894471/20000000000000000000)
  directionLo := (199075394761990874597/100000000000000000000)
  directionHi := (99537697380995437299/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree017.table
  base := (-8784230543400416843543329244075133717923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-4034357168049471148441042990800000000000000)
      constant := (20658839094039971864623937393466908820131317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree017.table
  base := (-881652259721082487671840675801473095311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-349563255910510650506517465938400000000000000)
      constant := (1797870940978834812784723397489052164656672270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199075394761990874597/100000000000000000000)
  centralHi := (99537697380995437299/50000000000000000000)
  directionLo := (205202220016305282259/100000000000000000000)
  directionHi := (10260111000815264113/5000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree018.table
  base := (-9492355664784697110934127179783433095719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-4233394527049863780288063639600000000000000)
      constant := (22827997325743201660104861742446204595418001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree018.table
  base := (-9520367054486977516261874532382408626297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-122274069169964393765104302651600000000000000)
      constant := (662272801679896567097313811067976835571860143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205202220016305282259/100000000000000000000)
  centralHi := (10260111000815264113/5000000000000000000)
  directionLo := (8446053696215559033/4000000000000000000)
  directionHi := (105575671202694487913/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree019.table
  base := (-2519840304243877284386169693295206275187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-4432431886050256412135084288400000000000000)
      constant := (25120376857500873457364025343645120162809492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree019.table
  base := (-10103692213052503189544729475203716416071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-384081159109275712084108349971200000000000000)
      constant := (2186482747646245799899983782479047589466970547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8446053696215559033/4000000000000000000)
  centralHi := (105575671202694487913/50000000000000000000)
  directionLo := (216937381978246140177/100000000000000000000)
  directionHi := (108468690989123070089/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree020.table
  base := (-5278216712944976963139235001202723405239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-4631469245050649043982104937200000000000000)
      constant := (27534624155977018035050106393708940935932162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree020.table
  base := (-2644394678078366971138960746241663465993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-401340110708658242872903791987600000000000000)
      constant := (2396748253681185561496282661299993233698540404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216937381978246140177/100000000000000000000)
  centralHi := (108468690989123070089/50000000000000000000)
  directionLo := (111286528833854290641/50000000000000000000)
  directionHi := (222573057667708581283/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree021.table
  base := (-85409052193328601105225234309594265689/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-4830506604051041675829125586000000000000000)
      constant := (30069676068076253827978772068613004013008768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree021.table
  base := (-2737683609950250453537290149557362772919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-139533020769346924553899744668000000000000000)
      constant := (872507995558340464422668105476163280749875844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111286528833854290641/50000000000000000000)
  centralHi := (222573057667708581283/100000000000000000000)
  directionLo := (45613903275001926181/20000000000000000000)
  directionHi := (114034758187504815453/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree022.table
  base := (-1401767042848323649924511180907243510503/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (378)
      previous := (0)
      next := (315)
      square := (16586446583366052653918387400000000000000)
      linear := (-457231269368312209788740566800000000000000)
      constant := (2974971424644382454107282032080162571075736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree022.table
  base := (-11230098278450276985355796852587818636073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-435858013907423304450494676020400000000000000)
      constant := (2848737483873261293945722818748425409983489661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45613903275001926181/20000000000000000000)
  centralHi := (114034758187504815453/50000000000000000000)
  directionLo := (46687318449235630803/20000000000000000000)
  directionHi := (7294893507693067313/3125000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree023.table
  base := (-2851851006699653944425417192282057367537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-5228581322051826939523166883600000000000000)
      constant := (35498970813623641210259485378135484234112092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree023.table
  base := (-713828724426164602711793147179743603531/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-453116965506805835239290118036800000000000000)
      constant := (3090330375562718959348679450388631000773212272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46687318449235630803/20000000000000000000)
  centralHi := (7294893507693067313/3125000000000000000)
  directionLo := (119341506714434960603/50000000000000000000)
  directionHi := (238683013428869921207/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree024.table
  base := (-11516741125238648775878207941099107211749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-5427618681052219571370187532400000000000000)
      constant := (38391977389195318993178311706327008027378371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree024.table
  base := (-11528758056118840609824472207139606725687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-156791972368729455342695186684400000000000000)
      constant := (1114085084624458481557716484250147028987883553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119341506714434960603/50000000000000000000)
  centralHi := (238683013428869921207/100000000000000000000)
  directionLo := (121908284377502166973/50000000000000000000)
  directionHi := (243816568755004333947/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree025.table
  base := (-11545891362929733671905470968043722752109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-5626656040052612203217208181200000000000000)
      constant := (41403252407099651841101029892866709546994811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree025.table
  base := (-5778151940356287852905965853900323982249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-487634868705570896816881002069600000000000000)
      constant := (3604473373120195748432876019190437833306747386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121908284377502166973/50000000000000000000)
  centralHi := (243816568755004333947/100000000000000000000)
  directionLo := (248844243452488593247/100000000000000000000)
  directionHi := (7776382607890268539/3125000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree026.table
  base := (-11497930064508663697528732934696578757513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-5825693399053004835064228830000000000000000)
      constant := (44532423753055587772986461652501713970340927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree026.table
  base := (-11506943564265195292473008192389729681181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-504893820304953427605676444086000000000000000)
      constant := (3876952918707174554148662737227674052939426817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248844243452488593247/100000000000000000000)
  centralHi := (7776382607890268539/3125000000000000000)
  directionLo := (253772330641894583587/100000000000000000000)
  directionHi := (63443082660473645897/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree027.table
  base := (-11375392609432893541364024375233957862809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-6024730758053397466911249478800000000000000)
      constant := (47779184646148774771512067290596691098600111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree027.table
  base := (-5691593688143823086662369644347956065259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-174050923968111986131490628700800000000000000)
      constant := (1386555891963269681450460394305049529873666842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253772330641894583587/100000000000000000000)
  centralHi := (63443082660473645897/25000000000000000000)
  directionLo := (25860652369844950429/10000000000000000000)
  directionHi := (258606523698449504291/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree028.table
  base := (-5590187439185330170161828858429893161559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-6223768117053790098758270127600000000000000)
      constant := (51143281484818356143111457003459965854902722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree028.table
  base := (-699194321578743515469132418492286766781/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-539411723503718489183267328118800000000000000)
      constant := (4452595987677282914270322845052560788712096272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25860652369844950429/10000000000000000000)
  centralHi := (258606523698449504291/100000000000000000000)
  directionLo := (263351993346119143369/100000000000000000000)
  directionHi := (26335199334611914337/10000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree029.table
  base := (-5457306477515567431447071351493212406517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-6422805476054182730605290776400000000000000)
      constant := (54624504202935522224797763112138642597622886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree029.table
  base := (-2730106374836174504030990184637210112493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-556670675103101019972062770135200000000000000)
      constant := (4755719927321692539536429261647934459180942404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263351993346119143369/100000000000000000000)
  centralHi := (26335199334611914337/10000000000000000000)
  directionLo := (67003363114917615141/25000000000000000000)
  directionHi := (53602690491934092113/20000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree030.table
  base := (-132244338762281299733354002533738765459/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-6621842835054575362452311425200000000000000)
      constant := (58222678528850522405350251871473408750356880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree030.table
  base := (-2646139874972353221871461985656955842033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-191309875567494516920286070717200000000000000)
      constant := (1689674877931129141654248116127712546855532508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67003363114917615141/25000000000000000000)
  centralHi := (53602690491934092113/20000000000000000000)
  directionLo := (54519042177694095851/20000000000000000000)
  directionHi := (34074401361058809907/12500000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree031.table
  base := (-10176373566390757280004159385718858401981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-6820880194054967994299332074000000000000000)
      constant := (61937659716293271944093609011928018133360299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree031.table
  base := (-10180692184778470506398559343955018803443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-591188578301866081549653654168000000000000000)
      constant := (5392497773513740471768550911786877738635644751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54519042177694095851/20000000000000000000)
  centralHi := (34074401361058809907/12500000000000000000)
  directionLo := (27710122211803280139/10000000000000000000)
  directionHi := (277101222118032801391/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree032.table
  base := (-970608683558385489527165685280460427721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-7019917553055360626146352722800000000000000)
      constant := (65769327432660087665495064944810642882457590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree032.table
  base := (-4854902296721571382534622435318355946937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-608447529901248612338449096184400000000000000)
      constant := (5726129101487970907583529685159940817692273818) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27710122211803280139/10000000000000000000)
  centralHi := (277101222118032801391/100000000000000000000)
  directionLo := (2815351232071853011/1000000000000000000)
  directionHi := (281535123207185301101/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree033.table
  base := (-9169514250751468221410520164360345140259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (378)
      previous := (0)
      next := (315)
      square := (16586446583366052653918387400000000000000)
      linear := (-656268628368704841635761215600000000000000)
      constant := (6337961960867819939138628641392036203457151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree033.table
  base := (-2293178050275789982590388203655787234887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-208568827166877047709081512733600000000000000)
      constant := (2023303367236119696410274529796496818541433412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815351232071853011/1000000000000000000)
  centralHi := (281535123207185301101/100000000000000000000)
  directionLo := (35737533643579534583/12500000000000000000)
  directionHi := (57180053829727255333/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree034.table
  base := (-4283672249472426948455301176036022761947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-7417992271056145889840394020400000000000000)
      constant := (73782338795817864885925887126599282491608826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree034.table
  base := (-8570093238411820765943296341966596344709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-642965433100013673916039980217200000000000000)
      constant := (6423833691412192617721449651582442834372203913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35737533643579534583/12500000000000000000)
  centralHi := (57180053829727255333/20000000000000000000)
  directionLo := (145099881288063361797/50000000000000000000)
  directionHi := (58039952515225344719/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree035.table
  base := (-1975037779632640920984214380621752355711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-7617029630056538521687414669200000000000000)
      constant := (77963529713333271568476021711779071859835876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree035.table
  base := (-7902512047573348919326205405119075480211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-660224384699396204704835422233600000000000000)
      constant := (6787893977173832785504442875845341494760156527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145099881288063361797/50000000000000000000)
  centralHi := (58039952515225344719/20000000000000000000)
  directionLo := (294436479565997353259/100000000000000000000)
  directionHi := (14721823978299867663/5000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree036.table
  base := (-28673647755106797259281333361696212553/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-7816066989056931153534435318000000000000000)
      constant := (82261096504750799068563262043408689570271750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree036.table
  base := (-7170438385725144029350415474143430793199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-225827778766259578497876954750000000000000000)
      constant := (2387362017773164576050465242488106717408874281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294436479565997353259/100000000000000000000)
  centralHi := (14721823978299867663/5000000000000000000)
  directionLo := (37326636517873288987/12500000000000000000)
  directionHi := (298613092142986311897/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree037.table
  base := (-6372525183314796659142230864721414766641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-8015104348057323785381455966800000000000000)
      constant := (86674990985011031545968282793368708813236439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree037.table
  base := (-3187131702315952488891794802359466848077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-694742287898161266282426306266400000000000000)
      constant := (7546405835051296695240008501148920175411063778) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37326636517873288987/12500000000000000000)
  centralHi := (298613092142986311897/100000000000000000000)
  directionLo := (302732087990641140629/100000000000000000000)
  directionHi := (30273208799064114063/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree038.table
  base := (-689102853422328393371143573720413804377/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-8214141707057716417228476615600000000000000)
      constant := (91205172985110682657653025543838639437363064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree038.table
  base := (-2757156447753384748954225316548665455279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-712001239497543797071221748282800000000000000)
      constant := (7940849920131602889421609722320164573301042806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302732087990641140629/100000000000000000000)
  centralHi := (30273208799064114063/10000000000000000000)
  directionLo := (38349473472418542941/12500000000000000000)
  directionHi := (306795787779348343529/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree039.table
  base := (-14342442776379454280100592450740088891/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-8413179066058109049075497264400000000000000)
      constant := (95851609010135491018066426823507343758140480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree039.table
  base := (-918171655556629914154254815759935598083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-243086730365642109286672396766400000000000000)
      constant := (2781805158042423063126044378575898320915365385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38349473472418542941/12500000000000000000)
  centralHi := (306795787779348343529/100000000000000000000)
  directionLo := (155403180227375497307/50000000000000000000)
  directionHi := (62161272090950198923/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree040.table
  base := (-450379080292271540473851044352890423507/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-8612216425058501680922517913200000000000000)
      constant := (100614271124109423926612692637066402070045224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree040.table
  base := (-3604125723245122753243791486758354467633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-746519142696308858648812632315600000000000000)
      constant := (8760100135126354473183167248847782504294508581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155403180227375497307/50000000000000000000)
  centralHi := (62161272090950198923/20000000000000000000)
  directionLo := (12590633470900898837/4000000000000000000)
  directionHi := (157382918386261235463/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree041.table
  base := (-127668414336366009420465032358055595199/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-8811253784058894312769538562000000000000000)
      constant := (105493136022715808669637143199293505459618420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree041.table
  base := (-1277151868364658192629920228294010227527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-763778094295691389437608074332000000000000000)
      constant := (9184901934572849841525782995627651302387871078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12590633470900898837/4000000000000000000)
  centralHi := (157382918386261235463/50000000000000000000)
  directionLo := (318676121319254034661/100000000000000000000)
  directionHi := (159338060659627017331/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree042.table
  base := (-1440749316924760083506364296558485736077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-9010291143059286944616559210800000000000000)
      constant := (110488184261821422421617516072116423225934683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree042.table
  base := (-288309891558726487624878483572613895489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-260345681965024640075467838782800000000000000)
      constant := (3206606410486117374706547519809418655149013955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318676121319254034661/100000000000000000000)
  centralHi := (159338060659627017331/50000000000000000000)
  directionLo := (322539003221411305249/100000000000000000000)
  directionHi := (1290156012885645221/400000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree043.table
  base := (-265309832876249837975325401135309175993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-9209328502059679576463579859600000000000000)
      constant := (115599399615332828485257718797662627589704847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree043.table
  base := (-265993901477556099465467353407155697449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-798295997494456451015198958364800000000000000)
      constant := (10064850657592803977150346527568969073051540093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322539003221411305249/100000000000000000000)
  centralHi := (1290156012885645221/400000000000000000)
  directionLo := (20397260357076682361/6250000000000000000)
  directionHi := (326356165713226917777/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree044.table
  base := (194567648364377056240743146671741217517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (378)
      previous := (0)
      next := (315)
      square := (16586446583366052653918387400000000000000)
      linear := (-855305987369097473482781864400000000000000)
      constant := (10984251685499533773023014476266945766963435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree044.table
  base := (243063420394411908895776526076806158137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-815554949093838981803994400381200000000000000)
      constant := (10519995072071758670273712327640880346837698764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20397260357076682361/6250000000000000000)
  centralHi := (326356165713226917777/100000000000000000000)
  directionLo := (82532298677175806213/25000000000000000000)
  directionHi := (330129194708703224853/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree045.table
  base := (1136800739517124358723786208325266420561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-9607403220060464840157621157200000000000000)
      constant := (126170279732503168492257271806414714473775762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree045.table
  base := (2273102176462272713317829950997205353197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-277604633564407170864263280799200000000000000)
      constant := (3661750507794071381056971443328421271834478757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82532298677175806213/25000000000000000000)
  centralHi := (330129194708703224853/100000000000000000000)
  directionLo := (333859586501562871923/100000000000000000000)
  directionHi := (83464896625390717981/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree046.table
  base := (3636901879116622292251373953558616216601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-9806440579060857472004641806000000000000000)
      constant := (131629923753400769052670967145980592562208721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree046.table
  base := (909118895796674837780672812346865239699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-850072852292604043381585284414000000000000000)
      constant := (11460619217856278796452093511498153254792706628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333859586501562871923/100000000000000000000)
  centralHi := (83464896625390717981/25000000000000000000)
  directionLo := (337548754699187415447/100000000000000000000)
  directionHi := (42193594337398426931/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree047.table
  base := (2531337157393481740461596165111329853601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-10005477938061250103851662454800000000000000)
      constant := (137205692722786546039006521967956941824571442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree047.table
  base := (2531155250618097214285112810425441787107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-867331803891986574170380726430400000000000000)
      constant := (11946097493402377272140625861673545777165516802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337548754699187415447/100000000000000000000)
  centralHi := (42193594337398426931/12500000000000000000)
  directionLo := (4264975456020927069/1250000000000000000)
  directionHi := (341198036481674165521/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree048.table
  base := (1637716100058546194867344142782331059613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-10204515297061642735698683103600000000000000)
      constant := (142897580059977357863280704504306648232852692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree048.table
  base := (6550554034445834608487186411866913010383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-294863585163789701653058722815600000000000000)
      constant := (4147228599208619758608803721902908724189143223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4264975456020927069/1250000000000000000)
  centralHi := (341198036481674165521/100000000000000000000)
  directionLo := (344808698264599339053/100000000000000000000)
  directionHi := (172404349132299669527/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree049.table
  base := (2025356678582434526051628185349163235801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-10403552656062035367545703752400000000000000)
      constant := (148705580269016650207367821668908995006127684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree049.table
  base := (8101162045580848361221945486467814982919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-901849707090751635747971610463200000000000000)
      constant := (12947383669601582088425297470979783391866623117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344808698264599339053/100000000000000000000)
  centralHi := (172404349132299669527/50000000000000000000)
  directionLo := (69676388166696806109/20000000000000000000)
  directionHi := (174190970416742015273/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree050.table
  base := (1942864663759661905636247757785825058081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-10602590015062427999392724401200000000000000)
      constant := (154629688759373110086106516653460424160139005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree050.table
  base := (4857048850979986917876996193282673426199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-919108658690134166536767052479600000000000000)
      constant := (13463190724685855292427077586772901917179592314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69676388166696806109/20000000000000000000)
  centralHi := (174190970416742015273/50000000000000000000)
  directionLo := (2815351232071853011/800000000000000000)
  directionHi := (43989863001122703297/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree051.table
  base := (11389522522151218649326962347892034800427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-10801627374062820631239745050000000000000000)
      constant := (160669901696376607170846731781694936210851667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree051.table
  base := (5694665131683413376225422305306067772613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-312122536763172232441854164832000000000000000)
      constant := (4663035547286199728933183166108140843832931706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2815351232071853011/800000000000000000)
  centralHi := (43989863001122703297/12500000000000000000)
  directionLo := (88855167723542000211/25000000000000000000)
  directionHi := (71084134178833600169/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree052.table
  base := (3281749462110964267843988599588886990513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-11000664733063213263086765698800000000000000)
      constant := (166826215876437843845640071842201021303408292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree052.table
  base := (13126834071712414603239641715630953181207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-953626561888899228114357936512400000000000000)
      constant := (14525131153172390422780908324028334044071344701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88855167723542000211/25000000000000000000)
  centralHi := (71084134178833600169/20000000000000000000)
  directionLo := (1401907311518737053/390625000000000000)
  directionHi := (358888271748796685569/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree053.table
  base := (2985345435355581427728531732810434969947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-11199702092063605894933786347600000000000000)
      constant := (173098628622928123674148584525550313156817935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree053.table
  base := (1492658770873293359736362620261117147943/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-970885513488281758903153378528800000000000000)
      constant := (15071264034956300097384281245322468463759687490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1401907311518737053/390625000000000000)
  centralHi := (358888271748796685569/100000000000000000000)
  directionLo := (18116134376489910663/5000000000000000000)
  directionHi := (362322687529798213261/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree054.table
  base := (1049293251448124085212333404559263012313/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-11398739451063998526780806996400000000000000)
      constant := (179487137699285457254356971210426733191837968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree054.table
  base := (16788573293671305592524950665342278391179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-329381488362554763230649606848400000000000000)
      constant := (5209168366827194014523217280581256471079694099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18116134376489910663/5000000000000000000)
  centralHi := (362322687529798213261/100000000000000000000)
  directionLo := (365724853132506500919/100000000000000000000)
  directionHi := (9143121328312662523/2500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree055.table
  base := (18712876941148633346981954426955219585499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (378)
      previous := (0)
      next := (315)
      square := (16586446583366052653918387400000000000000)
      linear := (-1054343346369490105329802513200000000000000)
      constant := (16908340112407890738184328234696507415440489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree055.table
  base := (1871277589759684585069305821829557753191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1005403416687046820480744262561600000000000000)
      constant := (16193854193845413120617767007736660716165736130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365724853132506500919/100000000000000000000)
  centralHi := (9143121328312662523/2500000000000000000)
  directionLo := (46136957545370268393/12500000000000000000)
  directionHi := (73819132072592429429/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree056.table
  base := (10349634510692369508490921381066230695863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-11796814169064783790474848294000000000000000)
      constant := (192612437672503323710398326871818027828398846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree056.table
  base := (10349591527464372871987709880201410326129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1022662368286429351269539704578000000000000000)
      constant := (16770311184869732944027545061898686656071530294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46136957545370268393/12500000000000000000)
  centralHi := (73819132072592429429/20000000000000000000)
  directionLo := (37243596066807077743/10000000000000000000)
  directionHi := (372435960668070777431/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree057.table
  base := (2843482184242722505004814256639256236789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-11995851528065176422321868942800000000000000)
      constant := (199349225701752714823132743344426800037211752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree057.table
  base := (22747784355981082088428046875364960978369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-346640439961937294019445048864800000000000000)
      constant := (5785625321615397139329686311066145429165702489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37243596066807077743/10000000000000000000)
  centralHi := (372435960668070777431/100000000000000000000)
  directionLo := (375746567647299234263/100000000000000000000)
  directionHi := (46968320955912404283/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree058.table
  base := (12429316639731877782121495603792492832359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-12194888887065569054168889591600000000000000)
      constant := (206202104232892895355149873771317783265430878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree058.table
  base := (24858571107051851153009283631309545095681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1057180271485194412847130588610800000000000000)
      constant := (17953548442986458517539040608739365579434196683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375746567647299234263/100000000000000000000)
  centralHi := (46968320955912404283/12500000000000000000)
  directionLo := (75805651873380543101/20000000000000000000)
  directionHi := (189514129683451357753/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree059.table
  base := (27031588897893151112811363700589586753331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-12393926246065961686015910240400000000000000)
      constant := (213171072353576906054758864978971339997153051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree059.table
  base := (3378942005853605875982623314482642725393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1770000000000000000000000000000000000000000
      center := (6111)
      previous := (0)
      next := (5040)
      square := (266891004114162847249414051800000000000000)
      linear := (-18210834289569100739591966620800000000000000)
      constant := (314581839719672048748338669420707422099156488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75805651873380543101/20000000000000000000)
  centralHi := (189514129683451357753/50000000000000000000)
  directionLo := (95570445123833174947/25000000000000000000)
  directionHi := (382281780495332699789/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree060.table
  base := (29266718025205764566215421137486465793817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-12592963605066354317862930889200000000000000)
      constant := (220256129301017818465496803509635862361051857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree060.table
  base := (14633336554878974673382031979584176828883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-363899391561319824808240490881200000000000000)
      constant := (6392405400975395605156678540393865039082683446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95570445123833174947/25000000000000000000)
  centralHi := (382281780495332699789/100000000000000000000)
  directionLo := (385507844276428944709/100000000000000000000)
  directionHi := (38550784427642894471/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree061.table
  base := (7891003847556902942568965429950344245677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-12792000964066746949709951538000000000000000)
      constant := (227457274437403580504707993845695966614907668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree061.table
  base := (6312795445715663061464081407488274476239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1108957126283342005213516914660000000000000000)
      constant := (19804211368465661353481179533327800251776819385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385507844276428944709/100000000000000000000)
  centralHi := (38550784427642894471/10000000000000000000)
  directionLo := (15548285374208285121/4000000000000000000)
  directionHi := (194353567177603564013/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree062.table
  base := (16961738292457245637945686135043059268731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-12991038323067139581556972186800000000000000)
      constant := (234774507229360843797051177092680420343032902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree062.table
  base := (33923444169526984686937077962141109320817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1126216077882724536002312356676400000000000000)
      constant := (20441313995865887896789735182934639604637291931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15548285374208285121/4000000000000000000)
  centralHi := (194353567177603564013/50000000000000000000)
  directionLo := (97970076617370361619/25000000000000000000)
  directionHi := (391880306469481446477/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree063.table
  base := (7269019584514240474972708558136553634139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-13190075682067532213403992835600000000000000)
      constant := (242207827230799489056834345640872614948654095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree063.table
  base := (36345070394796421793589262784390513019063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-381158343160702355597035932897600000000000000)
      constant := (7029508016060514116721295812644663375819358303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97970076617370361619/25000000000000000000)
  centralHi := (391880306469481446477/100000000000000000000)
  directionLo := (197513995009589357527/50000000000000000000)
  directionHi := (79005598003835743011/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree064.table
  base := (38828876319401518634186146557341270922831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-13389113041067924845251013484400000000000000)
      constant := (249757234068580172885663746056638293781662551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree064.table
  base := (38828852947728998444380655212788840810891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1160733981081489597579903240709200000000000000)
      constant := (21745841494536249102489650171724753864588134713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197513995009589357527/50000000000000000000)
  centralHi := (79005598003835743011/20000000000000000000)
  directionLo := (79630157904796349839/20000000000000000000)
  directionHi := (99537697380995437299/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree065.table
  base := (20687404597771142960237526214506548228227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-13588150400068317477098034133200000000000000)
      constant := (257422727430539453633399898471910584671230934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree065.table
  base := (2068739467849133457946790895367110609461/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1177992932680872128368698682725600000000000000)
      constant := (22413266309121783172815462692165374721892024460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79630157904796349839/20000000000000000000)
  centralHi := (99537697380995437299/25000000000000000000)
  directionLo := (50156160747357919829/12500000000000000000)
  directionHi := (401249285978863358633/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree066.table
  base := (8796578878474156096423079265354888334163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (378)
      previous := (0)
      next := (315)
      square := (16586446583366052653918387400000000000000)
      linear := (-1253380705369882737176823162000000000000000)
      constant := (24109482459589452884190673121194518858378965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree066.table
  base := (5497859694565910249332505064562596507581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-398417294760084886385831374914000000000000000)
      constant := (7696932823454197228134936146351539187543115688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50156160747357919829/12500000000000000000)
  centralHi := (401249285978863358633/100000000000000000000)
  directionLo := (80864807623223918227/20000000000000000000)
  directionHi := (12635126191128737223/3125000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree067.table
  base := (5831641262925601871275050262941093762543/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-13986225118069102740792075430800000000000000)
      constant := (273101972724829412494538543726526978762141624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree067.table
  base := (1457909869339126299522127257823240597893/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1212510835879637189946289566758400000000000000)
      constant := (23778437960218279401241722458393339250041491168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80864807623223918227/20000000000000000000)
  centralHi := (12635126191128737223/3125000000000000000)
  directionLo := (20368779179083302663/5000000000000000000)
  directionHi := (407375583581666053261/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree068.table
  base := (49385514816557569349559425885873869180473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-14185262477069495372639096079600000000000000)
      constant := (281115724255613240714467668743390738170837233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree068.table
  base := (49385502699199005296257055821923768809321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1229769787479019720735085008774800000000000000)
      constant := (24476184763601239128411635651533949917675739203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20368779179083302663/5000000000000000000)
  centralHi := (407375583581666053261/100000000000000000000)
  directionLo := (205202220016305282259/50000000000000000000)
  directionHi := (410404440032610564519/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree069.table
  base := (26090023632939181287905842023432215025739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-14384299836069888004486116728400000000000000)
      constant := (289245561494655433979514704564870596036228838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree069.table
  base := (521800369889996328544556017848001077843/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-415676246359467417174626816930400000000000000)
      constant := (8394679622630129866608091652829089175197148300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205202220016305282259/50000000000000000000)
  centralHi := (410404440032610564519/100000000000000000000)
  directionLo := (206705553081223665407/50000000000000000000)
  directionHi := (82682221232489466163/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree070.table
  base := (55036726391218740082433733455533874577491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-14583337195070280636333137377200000000000000)
      constant := (297491484313678029287130314572119598823876411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree070.table
  base := (5503671767699337673210663485898258655889/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1264287690677784782312675892807600000000000000)
      constant := (25902000262525136917653121322104355151434488270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206705553081223665407/50000000000000000000)
  centralHi := (82682221232489466163/20000000000000000000)
  directionLo := (416396062659622123747/100000000000000000000)
  directionHi := (104099015664905530937/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree071.table
  base := (57955551304520470204420658727996393285809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-14782374554070673268180158026000000000000000)
      constant := (305853492605225980605848904003687563587582889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree071.table
  base := (57955543916759126932135959136383302048819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1281546642277167313101471334824000000000000000)
      constant := (26630068938666305430198728914517050823295816817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416396062659622123747/100000000000000000000)
  centralHi := (104099015664905530937/25000000000000000000)
  directionLo := (209679886552342932629/50000000000000000000)
  directionHi := (419359773104685865259/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree072.table
  base := (60936521261636767874595679136459706412141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-14981411913071065900027178674800000000000000)
      constant := (314331586279257526942542082391511624475869061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree072.table
  base := (60936514999600361520072762046913125298001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-432935197958849947963422258946800000000000000)
      constant := (9122748296304325786299806346685304589162341481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209679886552342932629/50000000000000000000)
  centralHi := (419359773104685865259/100000000000000000000)
  directionLo := (8446053696215559033/2000000000000000000)
  directionHi := (422302684810777951651/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree073.table
  base := (12795927127755467501034614705909563258157/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-15180449272071458531874199323600000000000000)
      constant := (322925765260294042531087777476275285771184985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree073.table
  base := (15994907582975014621731855344247361759499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1316064545475932374679062218856800000000000000)
      constant := (28116528107066010142915313073944500795417792228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8446053696215559033/2000000000000000000)
  centralHi := (422302684810777951651/100000000000000000000)
  directionLo := (212612614805877007351/50000000000000000000)
  directionHi := (425225229611754014703/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree074.table
  base := (16771223478204379693067696032809800754563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-15379486631071851163721219972400000000000000)
      constant := (331636029485037443472296260267079943565208492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree074.table
  base := (13416977883241517656097189738104413845713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1333323497075314905467857660873200000000000000)
      constant := (28874918587930526857832640334944721968953904295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212612614805877007351/50000000000000000000)
  centralHi := (425225229611754014703/100000000000000000000)
  directionLo := (26757989037618117081/6250000000000000000)
  directionHi := (428127824601889873297/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree075.table
  base := (1405045912896736468114811574414521065721/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-15578523990072243795568240621200000000000000)
      constant := (340462378900378350685479594665207852447612050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree075.table
  base := (70252291835441755754345097091125038780369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-450194149558232478752217700963200000000000000)
      constant := (9881138775716982860912503905239206259994464489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26757989037618117081/6250000000000000000)
  centralHi := (428127824601889873297/100000000000000000000)
  directionLo := (431010872830749173817/100000000000000000000)
  directionHi := (215505436415374586909/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree076.table
  base := (1148153757286821090511866907038667697889/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-15777561349072636427415261270000000000000000)
      constant := (349404813461730841275486200665707442652452416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree076.table
  base := (3674091861984795834812341243521863790377/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1367841400274079967045448544906000000000000000)
      constant := (30422021321073200232121316486702776471258140220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431010872830749173817/100000000000000000000)
  centralHi := (215505436415374586909/50000000000000000000)
  directionLo := (216937381978246140177/50000000000000000000)
  directionHi := (86774952791298456071/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree077.table
  base := (76773528067833359893218981261602328232149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (378)
      previous := (0)
      next := (315)
      square := (16586446583366052653918387400000000000000)
      linear := (-1452418064370275369023843810800000000000000)
      constant := (32587575739240015576314813473877625610553639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree077.table
  base := (1535470506704320177580145306589410642853/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1385100351873462497834243986922400000000000000)
      constant := (31210733566629608134145573527962660767165693950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216937381978246140177/50000000000000000000)
  centralHi := (86774952791298456071/20000000000000000000)
  directionLo := (218359937430312264973/50000000000000000000)
  directionHi := (436719874860624529947/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree078.table
  base := (80127358189038540013843548730976797406809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-16175636067073421691109302567600000000000000)
      constant := (367637937878618666520523498463648192486223889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree078.table
  base := (80127355875193204205885329237842461037381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-467453101157615009541013142979600000000000000)
      constant := (10669851020414249232332005214888129606871123261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218359937430312264973/50000000000000000000)
  centralHi := (436719874860624529947/100000000000000000000)
  directionLo := (219773285113464829069/50000000000000000000)
  directionHi := (439546570226929658139/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree079.table
  base := (652682270398543073324379083533918438743/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-16374673426073814322956323216400000000000000)
      constant := (376928627676172339029605219344973328779251584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree079.table
  base := (20885832163018008954488626082967117050089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1419618255072227559411834870955200000000000000)
      constant := (32818479802745117180264873269238302413416317708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219773285113464829069/50000000000000000000)
  centralHi := (439546570226929658139/100000000000000000000)
  directionLo := (442355203087106077579/100000000000000000000)
  directionHi := (22117760154355303879/5000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree080.table
  base := (87021445149343006030889497281713344052703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-16573710785074206954803343865200000000000000)
      constant := (386335402501986940715447501747087314630377063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree080.table
  base := (87021443491124223731424176565126001926467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1436877206671610090200630312971600000000000000)
      constant := (33637513789312029156081421019197610838118094881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442355203087106077579/100000000000000000000)
  centralHi := (22117760154355303879/5000000000000000000)
  directionLo := (111286528833854290641/25000000000000000000)
  directionHi := (89029223067083432513/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree081.table
  base := (90561701648529738831859855297745285382531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-16772748144074599586650364514000000000000000)
      constant := (395858262337247300804761380988627179531286251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree081.table
  base := (90561700245079633893943013818779183662991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-484712052756997540329808584996000000000000000)
      constant := (11488885006468513871512317977741770338330871671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111286528833854290641/25000000000000000000)
  centralHi := (89029223067083432513/20000000000000000000)
  directionLo := (111979909553619866961/25000000000000000000)
  directionHi := (89583927642895893569/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree082.table
  base := (94164099977290005948567145593191071911713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-16971785503074992218497385162800000000000000)
      constant := (405497207166068090890923258480776119701317273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree082.table
  base := (2942628087176256529067464101622237050751/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1471395109870375151778221197004400000000000000)
      constant := (35305903491727609942460669353887712688671766176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111979909553619866961/25000000000000000000)
  centralHi := (89583927642895893569/20000000000000000000)
  directionLo := (28167255798383929411/6250000000000000000)
  directionHi := (450676092774142870577/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree083.table
  base := (24457160006154788292114106295051945748953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-17170822862075384850344405811600000000000000)
      constant := (415252236975017747814213986122005141742493252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree083.table
  base := (97828639019731430702070190310423817229083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1488654061469757682567016639020800000000000000)
      constant := (36155259205180940946937417631784355923323313769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28167255798383929411/6250000000000000000)
  centralHi := (450676092774142870577/100000000000000000000)
  directionLo := (113353947576315545857/25000000000000000000)
  directionHi := (453415790305262183429/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree084.table
  base := (101555321696500749865212112702133926841319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-17369860221075777482191426460400000000000000)
      constant := (425123351752720283468849378568158205147799599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree084.table
  base := (50777660423184927398838856821383164733533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-501971004356380071118604027012400000000000000)
      constant := (12338240719612093505990896631937669592874856746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113353947576315545857/25000000000000000000)
  centralHi := (453415790305262183429/100000000000000000000)
  directionLo := (456139032750019261811/100000000000000000000)
  directionHi := (114034758187504815453/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree085.table
  base := (105344144913153957060638432855168404559369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-17568897580076170114038447109200000000000000)
      constant := (435110551489522216338467747007475376951683649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree085.table
  base := (21068828838809055826464387079375576066267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1523171964668522744144607523053600000000000000)
      constant := (37884292351905075615196387135220595704300131405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456139032750019261811/100000000000000000000)
  centralHi := (114034758187504815453/25000000000000000000)
  directionLo := (11471152827258165369/2500000000000000000)
  directionHi := (458846113090326614761/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree086.table
  base := (27298777401682725350979151143138992522829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-17767934939076562745885467758000000000000000)
      constant := (445213836177213953747620018930879272381049236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree086.table
  base := (13649388624816603388730559393544321706837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1540430916267905274933402965070000000000000000)
      constant := (38763969783716625852314827383235066812675990328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11471152827258165369/2500000000000000000)
  centralHi := (458846113090326614761/100000000000000000000)
  directionLo := (115384328928931694869/25000000000000000000)
  directionHi := (461537315715726779477/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree087.table
  base := (22621643143878066024486542211695538026957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-17966972298076955377732488406800000000000000)
      constant := (455433205808796704110819910406075800506308985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree087.table
  base := (113108215205064186068939071314450986431597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-519229955955762601907399469028800000000000000)
      constant := (13217918151232995246735329783382603883768389157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115384328928931694869/25000000000000000000)
  centralHi := (461537315715726779477/100000000000000000000)
  directionLo := (232106458386047561819/50000000000000000000)
  directionHi := (464212916772095123639/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree088.table
  base := (23416692640337182483110789429540420415551/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (378)
      previous := (0)
      next := (315)
      square := (16586446583366052653918387400000000000000)
      linear := (-1651455423370668000870864459600000000000000)
      constant := (42342605488935223763744622909824723122855305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree088.table
  base := (117083462766798899538119584137596319205891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1574948819466670336510993849102800000000000000)
      constant := (40553646361363000391938143278470518361467119713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232106458386047561819/50000000000000000000)
  centralHi := (464212916772095123639/100000000000000000000)
  directionLo := (46687318449235630803/10000000000000000000)
  directionHi := (466873184492356308031/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree089.table
  base := (12112085201121765867746379585061580162857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-18365047016077740641426529704400000000000000)
      constant := (476220199880555826876429045181124511997056970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree089.table
  base := (121120851643546347302347462973161407603741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1592207771066052867299789291119200000000000000)
      constant := (41463645506288959160605641583821324579605867263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46687318449235630803/10000000000000000000)
  centralHi := (466873184492356308031/100000000000000000000)
  directionLo := (117379594877583872987/25000000000000000000)
  directionHi := (469518379510335491949/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree090.table
  base := (125220382111503376423002806296218085139229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-18564084375078133273273550353200000000000000)
      constant := (486787824311187455245830196369842388301846709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree090.table
  base := (125220381800697177751028548000201331960089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-536488907555145132696194911045200000000000000)
      constant := (14127917296038478862446349818396700836553069809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117379594877583872987/25000000000000000000)
  centralHi := (469518379510335491949/100000000000000000000)
  directionLo := (118037188789695926597/25000000000000000000)
  directionHi := (472148755158783706389/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree091.table
  base := (64691026735517071638335160182091401329321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-18763121734078525905120571002000000000000000)
      constant := (497471533666369766901958725941666119121695682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree091.table
  base := (129382053208329747291843998268086043835059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1626725674264817928877380175152000000000000000)
      constant := (43313965506529960948103781236529422555769521137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118037188789695926597/25000000000000000000)
  centralHi := (472148755158783706389/100000000000000000000)
  directionLo := (94952911550508389891/20000000000000000000)
  directionHi := (29672784859533871841/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree092.table
  base := (33401466515620920121853725695367865661737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-18962159093078918536967591650800000000000000)
      constant := (508271327942796282115937410228558046980280708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree092.table
  base := (133605865840462792877260239402043001038471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1643984625864200459666175617168400000000000000)
      constant := (44254286361261209912894443810643535059844752653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94952911550508389891/20000000000000000000)
  centralHi := (29672784859533871841/6250000000000000000)
  directionLo := (477366026857739842413/100000000000000000000)
  directionHi := (238683013428869921207/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree093.table
  base := (68945909931023222671532196496559402056257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-19161196452079311168814612299600000000000000)
      constant := (519187207137586530219593417803367375297614194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree093.table
  base := (13789181967443030048072204877925703007339/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-553747859154527663484990353061600000000000000)
      constant := (15068238150690827432410573662560793721685470590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477366026857739842413/100000000000000000000)
  centralHi := (238683013428869921207/50000000000000000000)
  directionLo := (119988348886965389043/25000000000000000000)
  directionHi := (479953395547861556173/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree094.table
  base := (17779989356110423313557981550306897993839/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-19360233811079703800661632948400000000000000)
      constant := (530219171248218986001373001095897077258036152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree094.table
  base := (3555997867258962219483267456437450207903/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1678502529062965521243766501201200000000000000)
      constant := (46165249778756236202760581349656651700845241160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119988348886965389043/25000000000000000000)
  centralHi := (479953395547861556173/100000000000000000000)
  directionLo := (60315861330931708427/12500000000000000000)
  directionHi := (482526890647453667417/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree095.table
  base := (146650151004657755514734408969465624792783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-19559271170080096432508653597200000000000000)
      constant := (541367220272474902896541816589305340599926743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree095.table
  base := (146650150870728132012580944971288594520287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1695761480662348052032561943217600000000000000)
      constant := (47135892341129518354864068645322166792575357141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60315861330931708427/12500000000000000000)
  centralHi := (482526890647453667417/100000000000000000000)
  directionLo := (60635841620524521619/12500000000000000000)
  directionHi := (485086732964196172953/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree096.table
  base := (151122528313146251378954601028526594609463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-19758308529080489064355674246000000000000000)
      constant := (552631354208391261486166367422051717947745023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree096.table
  base := (151122528200008206422152132308324453257683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 34810000000000000000000000000000000000000000
      center := (120183)
      previous := (0)
      next := (99120)
      square := (5248856414245202662571809685400000000000000)
      linear := (-571006810753910194273785795078000000000000000)
      constant := (16038880713010046090811346752558877421789994523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60635841620524521619/12500000000000000000)
  centralHi := (485086732964196172953/100000000000000000000)
  directionLo := (121908284377502166973/25000000000000000000)
  directionHi := (487633137510008667893/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree097.table
  base := (155657046759913186399689154566345275759943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-19957345888080881696202694894800000000000000)
      constant := (564011573054221343558372985438527778366953103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree097.table
  base := (194571308330436438175560286627768804439/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1730279383861113113610152827250400000000000000)
      constant := (49107499172313464985064390835338031699805181600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell192.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121908284377502166973/25000000000000000000)
  centralHi := (487633137510008667893/100000000000000000000)
  directionLo := (490166313711818306331/100000000000000000000)
  directionHi := (122541578427954576583/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree098.table
  base := (32050741266407475417548714164407555729063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4158)
      previous := (0)
      next := (3465)
      square := (182450912417026579193102261400000000000000)
      linear := (-20156383247081274328049715543600000000000000)
      constant := (575507876808401685910969136288666571216083115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree098.table
  base := (160253706251325955793042770068707217088993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (360549)
      previous := (0)
      next := (297360)
      square := (15746569242735607987715429056200000000000000)
      linear := (-1747538335460495644398948269266800000000000000)
      constant := (50108463440849744128212384795077109468060353899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell192.Kernel098
