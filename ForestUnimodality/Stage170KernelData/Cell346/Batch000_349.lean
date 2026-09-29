import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell346.Parameters
import ForestUnimodality.BinomialMassData.Q107_156.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_156.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_156.Batch100_149
import ForestUnimodality.BinomialMassData.Q9_13.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_13.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_13.Batch100_149

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel000
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
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree000.table
  base := (7196314576684378839779299201/1000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (2461)
      previous := (0)
      next := (1127)
      square := (16234100705056868571563021760000000000000)
      linear := (-27530759667310169963583277920000000000000)
      constant := (11226250739627630990055706753560000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree000.table
  base := (7196314576684378839779299201/1000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (207)
      previous := (0)
      next := (92)
      square := (1352841725421405714296918480000000000000)
      linear := (-2294229972275847496965273160000000000000)
      constant := (935520894968969249171308896130000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel001
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
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree001.table
  base := (26992267484050049272044849012433481262327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-1942224014745639097158369503040000000000000)
      constant := (329476217892297501858440371999910599999994936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree001.table
  base := (53817799032442175107202005702431065088757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-54176140697171320317893083720000000000000)
      constant := (9124285350830066671578907221910849999999933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29382451032349908141/100000000000000000000)
  directionHi := (14691225516174954071/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree002.table
  base := (20243106918028949392962166178883076512163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-2810748402466181565736991167200000000000000)
      constant := (248982457921881171385306529562409274999999384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree002.table
  base := (10059234749642111824811848886254387532873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-78527291754756623175237616360000000000000)
      constant := (6875055808646458652474507963027965972222148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29382451032349908141/100000000000000000000)
  centralHi := (14691225516174954071/50000000000000000000)
  directionLo := (1662122429828503513/4000000000000000000)
  directionHi := (20776530372856293913/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree003.table
  base := (30322752168397588124847517454725926070799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-1226424263395574678105204277120000000000000)
      constant := (63124567194438721572735007679324178071580372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree003.table
  base := (30042717399836010104021046589186510211209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-102878442812341926032582149000000000000000)
      constant := (5215026651195441648899346446732520225694321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1662122429828503513/4000000000000000000)
  centralHi := (20776530372856293913/50000000000000000000)
  directionLo := (12722974509733662681/25000000000000000000)
  directionHi := (2035675921557386029/4000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree004.table
  base := (22645550809061594492222755544574771278797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-4547797177907266502894234495520000000000000)
      constant := (145487071611148213391551399986792908460200948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree004.table
  base := (4473074301812210718583052147909070809811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-127229593869927228889926681640000000000000)
      constant := (3997207977582951782918721694903164834290295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12722974509733662681/25000000000000000000)
  centralHi := (2035675921557386029/4000000000000000000)
  directionLo := (58764902064699816283/100000000000000000000)
  directionHi := (14691225516174954071/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree005.table
  base := (8413008395461137304144850312023267858579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-5416321565627808971472856159680000000000000)
      constant := (113498208393372735691283715324999123303189272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree005.table
  base := (16562692005771004821858704198170462874921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-151580744927512531747271214280000000000000)
      constant := (3113066412649124226984578295690808225861649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58764902064699816283/100000000000000000000)
  centralHi := (14691225516174954071/25000000000000000000)
  directionLo := (8212644731736658367/12500000000000000000)
  directionHi := (65701157853893266937/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree006.table
  base := (12422464725184646686051210766155771902469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-2094948651116117146683825941280000000000000)
      constant := (30239966008187020808437119189603905418207132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree006.table
  base := (6092200532989453411050163132381588189159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-175931895985097834604615746920000000000000)
      constant := (2486505004140163253377988680744976807935742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8212644731736658367/12500000000000000000)
  centralHi := (65701157853893266937/100000000000000000000)
  directionLo := (17993003105392525567/25000000000000000000)
  directionHi := (71972012421570102269/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree007.table
  base := (9063306495207725893108794148815746254471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-7153370341068893908630099488000000000000000)
      constant := (74891398403069441873321902472655000212201564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree007.table
  base := (2213408044728786608999145828315367438439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-200283047042683137461960279560000000000000)
      constant := (2053833311736004238457193977261188388384764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17993003105392525567/25000000000000000000)
  centralHi := (71972012421570102269/100000000000000000000)
  directionLo := (77738658341130902739/100000000000000000000)
  directionHi := (3886932917056545137/5000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree008.table
  base := (81116998394055024623640830573573204773/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-8021894728789436377208721152160000000000000)
      constant := (64435844844819975216084264596289550227114560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree008.table
  base := (6308086079881862010633279403194790896949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-224634198100268440319304812200000000000000)
      constant := (1770722759702708562879695071299919661584381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77738658341130902739/100000000000000000000)
  centralHi := (3886932917056545137/5000000000000000000)
  directionLo := (83106121491425175651/100000000000000000000)
  directionHi := (20776530372856293913/25000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree009.table
  base := (4506935790853061541896816875218316199201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-2963473038836659615262447605440000000000000)
      constant := (19391611029602442227709809047042745251979628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree009.table
  base := (4352345746285168145497752480992303856823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-248985349157853743176649344840000000000000)
      constant := (1604147871221909593958852075807699351803087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83106121491425175651/100000000000000000000)
  centralHi := (20776530372856293913/25000000000000000000)
  directionLo := (3525894123881988977/4000000000000000000)
  directionHi := (44073676548524862213/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree010.table
  base := (2971072353248604025407916588666966687591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-9758943504230521314365964480480000000000000)
      constant := (55226414935765504323119944595049825327303644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree010.table
  base := (568119362572789588275745883965462148033/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-273336500215439046033993877480000000000000)
      constant := (1529466018564478575727959832350815515087885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3525894123881988977/4000000000000000000)
  centralHi := (44073676548524862213/50000000000000000000)
  directionLo := (92915468500591449297/100000000000000000000)
  directionHi := (46457734250295724649/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree011.table
  base := (886545048049229634052128135939158528207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-10627467891951063782944586144640000000000000)
      constant := (54929384535159631329339055089527680971222776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree011.table
  base := (1663844416048041960710197527952053897217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-297687651273024348891338410120000000000000)
      constant := (1528257069787058563238362196023897108629673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92915468500591449297/100000000000000000000)
  centralHi := (46457734250295724649/50000000000000000000)
  directionLo := (97450565495295315961/100000000000000000000)
  directionHi := (48725282747647657981/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree012.table
  base := (831361668381623676906186798976917012903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-3831997426557202083841069269600000000000000)
      constant := (18929040361125973947163391114245187702167284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree012.table
  base := (740462404333846040520316911849128024609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-322038802330609651748682942760000000000000)
      constant := (1586726205285540452947818224822502636158921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97450565495295315961/100000000000000000000)
  centralHi := (48725282747647657981/50000000000000000000)
  directionLo := (12722974509733662681/12500000000000000000)
  directionHi := (101783796077869301449/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree013.table
  base := (84461394573591454790957100188507501771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (7383)
      previous := (0)
      next := (3381)
      square := (48702302115170605714689065280000000000000)
      linear := (-951116666722472978469371497920000000000000)
      constant := (4648146982348406353114375526628221510828828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree013.table
  base := (4600697419738380688189909767425262697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (207)
      previous := (0)
      next := (92)
      square := (1352841725421405714296918480000000000000)
      linear := (-26645381029861150354309805800000000000000)
      constant := (130347867642529688228630792973953056830122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12722974509733662681/12500000000000000000)
  centralHi := (101783796077869301449/100000000000000000000)
  directionLo := (105939933795947420231/100000000000000000000)
  directionHi := (13242491724493427529/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree014.table
  base := (-64240588914007418856949874836820213709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-13233041055112691188680451137120000000000000)
      constant := (65563979305872322416624593595942286558355552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree014.table
  base := (-143997567347842406801640630287214462647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-370741104445780257463372008040000000000000)
      constant := (1843862561963479711479552105045843023250628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105939933795947420231/100000000000000000000)
  centralHi := (13242491724493427529/12500000000000000000)
  directionLo := (109939064946715653599/100000000000000000000)
  directionHi := (137423831183394567/125000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree015.table
  base := (-998786182777002886784170217475340796289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-4700521814277744552419690933760000000000000)
      constant := (23996150122527618603690706140260008865125908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree015.table
  base := (-1049808291330368183278398308615086469677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-395092255503365560320716540680000000000000)
      constant := (2028883479315108661659442508444050386624587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109939064946715653599/100000000000000000000)
  centralHi := (137423831183394567/125000000000000000)
  directionLo := (2275954870380922359/2000000000000000000)
  directionHi := (113797743519046117951/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree016.table
  base := (-1396610391093612910424941255270025796949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-14970089830553776125837694465440000000000000)
      constant := (79538174788839760833624212611257163051362284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree016.table
  base := (-1438446786079773493115229602829188826219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-419443406560950863178061073320000000000000)
      constant := (2245158225955491772431210270721867088368989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2275954870380922359/2000000000000000000)
  centralHi := (113797743519046117951/100000000000000000000)
  directionLo := (117529804129399632567/100000000000000000000)
  directionHi := (14691225516174954071/12500000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree017.table
  base := (-863744616537919496785868308303528290981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-15838614218274318594416316129600000000000000)
      constant := (88090913469426968289487247881822667755343192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree017.table
  base := (-880861325222497431347653316056764618971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-443794557618536166035405605960000000000000)
      constant := (2489337746324514871084531103292813558787802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117529804129399632567/100000000000000000000)
  centralHi := (14691225516174954071/12500000000000000000)
  directionLo := (121146949145917344087/100000000000000000000)
  directionHi := (15143368643239668011/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree018.table
  base := (-2006694396928314933495814695288819669533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-5569046201998287020998312597920000000000000)
      constant := (32517917819435828718687629388194273710187076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree018.table
  base := (-20346594676202096421805827635530937157/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-468145708676121468892750138600000000000000)
      constant := (2758883054862361985442034887119527162046700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121146949145917344087/100000000000000000000)
  centralHi := (15143368643239668011/12500000000000000000)
  directionLo := (31164795559284440869/25000000000000000000)
  directionHi := (124659182237137763477/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree019.table
  base := (-224585739044858715721535869173569289273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-17575662993715403531573559457920000000000000)
      constant := (107855928662041041971372506868180044440630680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree019.table
  base := (-567167662137134514926555833497839200877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-492496859733706771750094671240000000000000)
      constant := (3051865285119645796948878680275460700207148) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31164795559284440869/25000000000000000000)
  centralHi := (124659182237137763477/100000000000000000000)
  directionLo := (64037567381772793789/50000000000000000000)
  directionHi := (128075134763545587579/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree020.table
  base := (-1198171458841003563846361768614427973/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-18444187381435946000152181122080000000000000)
      constant := (118943431813747461481995955870687631794724864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree020.table
  base := (-2472444910912633421174015569303834448301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-516848010791292074607439203880000000000000)
      constant := (3366816043807997896907660441587651978237131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64037567381772793789/50000000000000000000)
  centralHi := (128075134763545587579/100000000000000000000)
  directionLo := (8212644731736658367/6250000000000000000)
  directionHi := (131402315707786533873/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree021.table
  base := (-527495189369220069801964599726630661379/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-6437570589718829489576934262080000000000000)
      constant := (43591654343065362459790137991511965093616940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree021.table
  base := (-1326305145117073861418752694897884912307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-541199161848877377464783736520000000000000)
      constant := (3702615192924259097951530910524514899640234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8212644731736658367/6250000000000000000)
  centralHi := (131402315707786533873/100000000000000000000)
  directionLo := (67323652979538409471/50000000000000000000)
  directionHi := (134647305959076818943/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree022.table
  base := (-2801921116088668144149109458087646532639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-20181236156877030937309424450400000000000000)
      constant := (143318877427490928556199098726754758495424324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree022.table
  base := (-2814233076658720133726017942171094042307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-565550312906462680322128269160000000000000)
      constant := (4058406529433816380514534137293085106850117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67323652979538409471/50000000000000000000)
  centralHi := (134647305959076818943/100000000000000000000)
  directionLo := (34453977846093551629/25000000000000000000)
  directionHi := (137815911384374206517/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree023.table
  base := (-2951183773607122665989301117077096944763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-21049760544597573405888046114560000000000000)
      constant := (156550880877667185427125069309522942188061908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree023.table
  base := (-148059674084360341652911375958838803761/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-589901463964047983179472801800000000000000)
      constant := (4433534297593025050308714166419124843287820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34453977846093551629/25000000000000000000)
  centralHi := (137815911384374206517/100000000000000000000)
  directionLo := (2818265697862720977/2000000000000000000)
  directionHi := (140913284893136048851/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree024.table
  base := (-3088335315494493165704476688880704474423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-7306094977439371958155555926240000000000000)
      constant := (56817429001964956009335076943749931325870156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree024.table
  base := (-193529317221841694647282819443156026377/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-614252615021633286036817334440000000000000)
      constant := (4827495288033038886728786920545706104676592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2818265697862720977/2000000000000000000)
  centralHi := (140913284893136048851/100000000000000000000)
  directionLo := (17993003105392525567/12500000000000000000)
  directionHi := (143944024843140204537/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree025.table
  base := (-3215742561986023052119134198205233376457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-22786809320038658343045289442880000000000000)
      constant := (185008696077862755459551337309619360137635612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree025.table
  base := (-3222349083651631604175142917578199022607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-638603766079218588894161867080000000000000)
      constant := (5239902621660221813887087157929284365179417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17993003105392525567/12500000000000000000)
  centralHi := (143944024843140204537/100000000000000000000)
  directionLo := (146912255161749540709/100000000000000000000)
  directionHi := (14691225516174954071/10000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree026.table
  base := (-416904085091724283668234902531290100409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (7383)
      previous := (0)
      next := (3381)
      square := (48702302115170605714689065280000000000000)
      linear := (-1819641054443015447047993162080000000000000)
      constant := (15400691661967352397983253571162849864068704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree026.table
  base := (-835149186616288764483351898217179177309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (207)
      previous := (0)
      next := (92)
      square := (1352841725421405714296918480000000000000)
      linear := (-50996532087446453211654338440000000000000)
      constant := (436189100833453690624442205692706682779932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146912255161749540709/100000000000000000000)
  centralHi := (14691225516174954071/10000000000000000000)
  directionLo := (1498216911711366471/1000000000000000000)
  directionHi := (149821691171136647101/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree027.table
  base := (-689643740322794067053153376158369986599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-8174619365159914426734177590400000000000000)
      constant := (72014858905088922109303256264174128335886140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree027.table
  base := (-863143146645599838758699204163537647093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-687306068194389194608850932360000000000000)
      constant := (6118932427238958221801583740905448550565132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1498216911711366471/1000000000000000000)
  centralHi := (149821691171136647101/100000000000000000000)
  directionLo := (38168923529200988043/25000000000000000000)
  directionHi := (152675694116803952173/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree028.table
  base := (-3555795233322529911080606406097071180621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-25392382483200285748781154435360000000000000)
      constant := (232508791807629976747181947079225418937101836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree028.table
  base := (-111229005926754530152398362996536050789/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-711657219251974497466195465000000000000000)
      constant := (6585147252897082645610425501074733037333088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38168923529200988043/25000000000000000000)
  centralHi := (152675694116803952173/100000000000000000000)
  directionLo := (155477316682261805479/100000000000000000000)
  directionHi := (3886932917056545137/2500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree029.table
  base := (-1829405801368369146573812731126246084613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-26260906870920828217359776099520000000000000)
      constant := (249596469577943930368561458164755837642429016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree029.table
  base := (-915419424719466075955131946031911933537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-736008370309559800323539997640000000000000)
      constant := (7068965197609912411179219697402427532928988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155477316682261805479/100000000000000000000)
  centralHi := (3886932917056545137/2500000000000000000)
  directionLo := (158229341246763601947/100000000000000000000)
  directionHi := (39557335311690900487/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree030.table
  base := (-469740981665520735464936915882717691887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-9043143752880456895312799254560000000000000)
      constant := (89101198107250642954914349998318788166825312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree030.table
  base := (-1880126214762791773978244500775612969537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-760359521367145103180884530280000000000000)
      constant := (7570279569095461094748696895937842816296494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158229341246763601947/100000000000000000000)
  centralHi := (39557335311690900487/25000000000000000000)
  directionLo := (8046715612604499999/5000000000000000000)
  directionHi := (160934312252089999981/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree031.table
  base := (-77073154067807630950195188002952555737/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-27997955646361913154517019427840000000000000)
      constant := (285627040576882891262809524526521832544804600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree031.table
  base := (-3855542671857160671309328000724660686691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-784710672424730406038229062920000000000000)
      constant := (8089007508300150698708683348877532343949221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8046715612604499999/5000000000000000000)
  centralHi := (160934312252089999981/100000000000000000000)
  directionLo := (40898640937629001537/25000000000000000000)
  directionHi := (163594563750516006149/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree032.table
  base := (-157856062550271410254740964829335387179/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-28866480034082455623095641092000000000000000)
      constant := (304564372243899420134024834183218087610074100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree032.table
  base := (-986982437485265244644816157978586267379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-809061823482315708895573595560000000000000)
      constant := (8625084571456410586564841901526475683251796) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40898640937629001537/25000000000000000000)
  centralHi := (163594563750516006149/100000000000000000000)
  directionLo := (83106121491425175651/50000000000000000000)
  directionHi := (166212242982850351303/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree033.table
  base := (-2018235981224096055969288902494871281411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-9911668140600999363891420918720000000000000)
      constant := (108037895967432846799998084949820802082596984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree033.table
  base := (-7886153621652427538927062483642525909/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-833412974539901011752918128200000000000000)
      constant := (9178460567168260583619396204575379518146048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83106121491425175651/50000000000000000000)
  centralHi := (166212242982850351303/100000000000000000000)
  directionLo := (33757866132834004133/20000000000000000000)
  directionHi := (84394665332085010333/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree034.table
  base := (-64439268094201159926633064835662127371/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-30603528809523540560252884420320000000000000)
      constant := (344273501482975220476039106307349223492789504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree034.table
  base := (-412511700329478048653518922363576692039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-857764125597486314610262660840000000000000)
      constant := (9749096351925648775224331130725555390454090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33757866132834004133/20000000000000000000)
  centralHi := (84394665332085010333/50000000000000000000)
  directionLo := (171327658522279951843/100000000000000000000)
  directionHi := (42831914630569987961/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree035.table
  base := (-4209516296474227735645147900867962827181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-31472053197244083028831506084480000000000000)
      constant := (365042650053815150433915516142219314159430796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree035.table
  base := (-4210329665174845823230227536656995967379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-882115276655071617467607193480000000000000)
      constant := (10336961359001495479042132297704967681512949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171327658522279951843/100000000000000000000)
  centralHi := (42831914630569987961/25000000000000000000)
  directionLo := (10864307783149983377/6250000000000000000)
  directionHi := (173828924530399734033/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree036.table
  base := (-536603893003176930205349140039522854861/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-10780192528321541832470042582880000000000000)
      constant := (128806740812335698541306749700638781202735136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree036.table
  base := (-4293490052789078530495971931536284090869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-906466427712656920324951726120000000000000)
      constant := (10942031689621980799211645736370367988643139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10864307783149983377/6250000000000000000)
  centralHi := (173828924530399734033/100000000000000000000)
  directionLo := (176294706194099448851/100000000000000000000)
  directionHi := (44073676548524862213/25000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree037.table
  base := (-4374175184356046093418798561990493138019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-33209101972685167965988749412800000000000000)
      constant := (408405503861880820471155031534109839748292404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree037.table
  base := (-21873544314258736523553942799896607201/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-930817578770242223182296258760000000000000)
      constant := (11564288636042393326044927567083494676606200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176294706194099448851/100000000000000000000)
  centralHi := (44073676548524862213/25000000000000000000)
  directionLo := (178726472187900264503/100000000000000000000)
  directionHi := (22340809023487533063/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree038.table
  base := (-139176271349452618611496164750133084697/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-34077626360405710434567371076960000000000000)
      constant := (430997932983817965763265629266246090006510464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree038.table
  base := (-1113518212099177907483012146567544793909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-955168729827827526039640791400000000000000)
      constant := (12203717537000010806736282063080339719317516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178726472187900264503/100000000000000000000)
  centralHi := (22340809023487533063/12500000000000000000)
  directionLo := (90562796292684015907/50000000000000000000)
  directionHi := (36225118517073606363/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree039.table
  base := (-4531300182665087293685761859841119441011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (2461)
      previous := (0)
      next := (1127)
      square := (16234100705056868571563021760000000000000)
      linear := (-896055147387852638542204942080000000000000)
      constant := (11646078678367048945949938592364785367202284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree039.table
  base := (-2265825037514240281711341222720791987329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (207)
      previous := (0)
      next := (92)
      square := (1352841725421405714296918480000000000000)
      linear := (-75347683145031756068998871080000000000000)
      constant := (989254376108282400816021075449259408329446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90562796292684015907/50000000000000000000)
  centralHi := (36225118517073606363/20000000000000000000)
  directionLo := (45873336971266031339/25000000000000000000)
  directionHi := (183493347885064125357/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree040.table
  base := (-4607210780707984826400340538295477346203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-35814675135846795371724614405280000000000000)
      constant := (478002562895722933653688887155410315825700948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree040.table
  base := (-4607494006257620309386405779283102816053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1003871031942998131754329856680000000000000)
      constant := (13534047657932088849150475376901155624087043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45873336971266031339/25000000000000000000)
  centralHi := (183493347885064125357/100000000000000000000)
  directionLo := (92915468500591449297/50000000000000000000)
  directionHi := (37166187400236579719/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree041.table
  base := (-4681417468412239192167023356311001849329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-36683199523567337840303236069440000000000000)
      constant := (502414142576183173982386760688023864748682364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree041.table
  base := (-4681646683087365139892916779945391239253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1028222183000583434611674389320000000000000)
      constant := (14224932737643717130383107256789228880566243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92915468500591449297/50000000000000000000)
  centralHi := (37166187400236579719/20000000000000000000)
  directionLo := (188139484360423523223/100000000000000000000)
  directionHi := (23517435545052940403/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree042.table
  base := (-4753955736336723543314785069180115515989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-12517241303762626769627285911200000000000000)
      constant := (175810530524378481873123914429622725733574308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree042.table
  base := (-4754141201858065685915294792685800897489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1052573334058168737469018921960000000000000)
      constant := (14932956535261036797671719211156099648324359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188139484360423523223/100000000000000000000)
  centralHi := (23517435545052940403/12500000000000000000)
  directionLo := (1487656611127547637/781250000000000000)
  directionHi := (190420046224326097537/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree043.table
  base := (-4824853612250202835445469329312860152597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-38420248299008422777460479397760000000000000)
      constant := (553054739365634582574762218176680558831599852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree043.table
  base := (-4825003647583973746074739167371747134847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1076924485115754040326363454600000000000000)
      constant := (15658114642416639297049328549874174734210857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1487656611127547637/781250000000000000)
  centralHi := (190420046224326097537/100000000000000000000)
  directionLo := (48168404084487094319/25000000000000000000)
  directionHi := (192673616337948377277/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree044.table
  base := (-4894133256226992337664255109426682915739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-39288772686728965246039101061920000000000000)
      constant := (579283451131788450751322276481448061140643924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree044.table
  base := (-1223563651044446077073568572694316494753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1101275636173339343183707987240000000000000)
      constant := (16400403580429279175556944151578642049546972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48168404084487094319/25000000000000000000)
  centralHi := (192673616337948377277/100000000000000000000)
  directionLo := (97450565495295315961/50000000000000000000)
  directionHi := (194901130990590631923/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree045.table
  base := (-992362442121372080238505464772585250659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-13385765691483169238205907575360000000000000)
      constant := (202039206714667299833407004128105985558317740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree045.table
  base := (-4961910335444124523631366841436588713161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1125626787230924646041052519880000000000000)
      constant := (17159820600715974444665854147597216507475791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97450565495295315961/50000000000000000000)
  centralHi := (194901130990590631923/100000000000000000000)
  directionLo := (24637934195209975101/12500000000000000000)
  directionHi := (197103473561679800809/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree046.table
  base := (-5027904380506053296430701706957753197193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-41025821462170050183196344390240000000000000)
      constant := (633557161803547686512342296557589029548277788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree046.table
  base := (-5027983709560744252541083963902168099609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1149977938288509948898397052520000000000000)
      constant := (17936363528554685377959152190500533591166079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24637934195209975101/12500000000000000000)
  centralHi := (197103473561679800809/100000000000000000000)
  directionLo := (199281478614416769899/100000000000000000000)
  directionHi := (1992814786144167699/1000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree047.table
  base := (-1018484160742016471520067465118177112229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-41894345849890592651774966054400000000000000)
      constant := (661602008956538760830282163638365052245993820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree047.table
  base := (-1018496984691967052238809302772181077611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1174329089346095251755741585160000000000000)
      constant := (18730030640663871566954003355677506989418705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199281478614416769899/100000000000000000000)
  centralHi := (1992814786144167699/1000000000000000000)
  directionLo := (8057437423639522237/4000000000000000000)
  directionHi := (100717967795494027963/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree048.table
  base := (-41242962045943941337188823627036224063/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-14254290079203711706784529239520000000000000)
      constant := (230084036070895610724144012935986317200029500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree048.table
  base := (-2577711035467752507278200378003421983851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1198680240403680554613086117800000000000000)
      constant := (19540820569192328850071128924394843369458362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8057437423639522237/4000000000000000000)
  centralHi := (100717967795494027963/50000000000000000000)
  directionLo := (12722974509733662681/6250000000000000000)
  directionHi := (203567592155738602897/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree049.table
  base := (-1304189931452401336804593459200626032899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-43631394625331677588932209382720000000000000)
      constant := (719507417049669768831674669066793564863369936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree049.table
  base := (-5216801588572084904175169502477441325129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1223031391461265857470430650440000000000000)
      constant := (20368732226357305222139082041401312416053199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12722974509733662681/6250000000000000000)
  centralHi := (203567592155738602897/100000000000000000000)
  directionLo := (205677157226449356993/100000000000000000000)
  directionHi := (102838578613224678497/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree050.table
  base := (-211063791658886594043262362986964845909/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-44499919013052220057510831046880000000000000)
      constant := (749367901533598875554303759457682646937241100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree050.table
  base := (-5276628606051967178315508135785747205779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1247382542518851160327775183080000000000000)
      constant := (21213764745242476393201051447052208722223349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205677157226449356993/100000000000000000000)
  centralHi := (102838578613224678497/50000000000000000000)
  directionLo := (207765303728562939127/100000000000000000000)
  directionHi := (25970662966070367391/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree051.table
  base := (-1066975982766882541535819512075866414469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-15122814466924254175363150903680000000000000)
      constant := (259944511507706329626080879251090714557284340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree051.table
  base := (-5334907221556833811495488029047051987603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1271733693576436463185119715720000000000000)
      constant := (22075917433255138109563483079291048214095093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207765303728562939127/100000000000000000000)
  centralHi := (25970662966070367391/12500000000000000000)
  directionLo := (209832671102691845131/100000000000000000000)
  directionHi := (52458167775672961283/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree052.table
  base := (-1347904667567015141451915123043018747009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (7383)
      previous := (0)
      next := (3381)
      square := (48702302115170605714689065280000000000000)
      linear := (-3556689829884100384205236490400000000000000)
      constant := (62377253404115431933247104337183468905599152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree052.table
  base := (-53916407184363370356758265263122625879/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (207)
      previous := (0)
      next := (92)
      square := (1352841725421405714296918480000000000000)
      linear := (-99698834202617058926343403720000000000000)
      constant := (1765783825808399934155770438997940586357300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209832671102691845131/100000000000000000000)
  centralHi := (52458167775672961283/25000000000000000000)
  directionLo := (211879867591894840463/100000000000000000000)
  directionHi := (13242491724493427529/6250000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree053.table
  base := (-272340696901216049680755673995454122473/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-47105492176213847463246696039360000000000000)
      constant := (842580163219547377051601300977653142377485360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree053.table
  base := (-544683173578724392797929912424837363657/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1320435995691607068899808781000000000000000)
      constant := (23851581205997305860551900271162024855419670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211879867591894840463/100000000000000000000)
  centralHi := (13242491724493427529/6250000000000000000)
  directionLo := (13369217020744446221/6250000000000000000)
  directionHi := (213907472331911139537/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree054.table
  base := (-1100093607838394484086898190067445999899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-15991338854644796643941772567840000000000000)
      constant := (291620375764557048890782430027916097561024140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree054.table
  base := (-5500482402836013471233962722840179111963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1344787146749192371757153313640000000000000)
      constant := (24765091484880186691046195155760009730078253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13369217020744446221/6250000000000000000)
  centralHi := (213907472331911139537/100000000000000000000)
  directionLo := (53979009316177576701/25000000000000000000)
  directionHi := (43183207452942061361/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree055.table
  base := (-2776291427606192442341683238382899316251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-48842540951654932400403939367680000000000000)
      constant := (907747175029182628680717806081656881119857832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree055.table
  base := (-5552594444873334573712847639531566565459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1369138297806777674614497846280000000000000)
      constant := (25695720280583715210009758237119165250437429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53979009316177576701/25000000000000000000)
  centralHi := (43183207452942061361/20000000000000000000)
  directionLo := (108953044446637894361/50000000000000000000)
  directionHi := (217906088893275788723/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree056.table
  base := (-2801579958700563257149907786040795357271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-49711065339375474868982561031840000000000000)
      constant := (941238297109557906586337597550975602092726472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree056.table
  base := (-1400792316703749964737839869188640778647/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1393489448864362977471842378920000000000000)
      constant := (26643467355677122464065105968428478833634628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108953044446637894361/50000000000000000000)
  centralHi := (217906088893275788723/100000000000000000000)
  directionLo := (109939064946715653599/50000000000000000000)
  directionHi := (219878129893431307199/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree057.table
  base := (-1413050119636727049006246559987134642223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-16859863242365339112520394232000000000000000)
      constant := (325111495304276821118091173345804363782287024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree057.table
  base := (-5652208019155050378767861985963575037033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1417840599921948280329186911560000000000000)
      constant := (27608332515726915515454934875692155818741423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109939064946715653599/50000000000000000000)
  centralHi := (219878129893431307199/100000000000000000000)
  directionLo := (221832640596691925179/100000000000000000000)
  directionHi := (11091632029834596259/5000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree058.table
  base := (-569970556957772753500837644728268829707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-51448114114816559806139804360160000000000000)
      constant := (1010035735166834361554796027910252124400626120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree058.table
  base := (-1424927912513364294384542468392663279501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1442191750979533583186531444200000000000000)
      constant := (28590315600494059257679732273526559623057324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221832640596691925179/100000000000000000000)
  centralHi := (11091632029834596259/5000000000000000000)
  directionLo := (55942520089133414569/25000000000000000000)
  directionHi := (223770080356533658277/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree059.table
  base := (-287283802221796121099949622241809273223/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-52316638502537102274718426024320000000000000)
      constant := (1045342039676184417460588167139916647634225360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree059.table
  base := (-2872840473249477812156560686535055828379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1466542902037118886043875976840000000000000)
      constant := (29589416476977457413369906500471151130007898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55942520089133414569/25000000000000000000)
  centralHi := (223770080356533658277/100000000000000000000)
  directionLo := (22569088880909209353/10000000000000000000)
  directionHi := (225690888809092093531/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree060.table
  base := (-5790112615637711326543630101635073373491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-17728387630085881581099015896160000000000000)
      constant := (360417798368643985967642410553084071198560252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree060.table
  base := (-1447529141714824497374292652050875747643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1490894053094704188901220509480000000000000)
      constant := (30605635033912959848827104809613607994593332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22569088880909209353/10000000000000000000)
  centralHi := (225690888809092093531/100000000000000000000)
  directionLo := (2275954870380922359/1000000000000000000)
  directionHi := (227595487038092235901/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree061.table
  base := (-2916507941234585076506071885383144346153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-54053687277978187211875669352640000000000000)
      constant := (1117769797810020497079627027584077899596010296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree061.table
  base := (-5833019066638260061305784845602158499887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1515245204152289491758565042120000000000000)
      constant := (31638971177420428455842913232893235213519097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2275954870380922359/1000000000000000000)
  centralHi := (227595487038092235901/100000000000000000000)
  directionLo := (22948427865275401289/10000000000000000000)
  directionHi := (229484278652754012891/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree062.table
  base := (-734298294169832171802608089471771091779/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-54922211665698729680454291016800000000000000)
      constant := (1154891244695171902040856195506989957420932512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree062.table
  base := (-5874388918871739194751691194921521967007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1539596355209874794615909574760000000000000)
      constant := (32689424827556796581420180888778262787575817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22948427865275401289/10000000000000000000)
  centralHi := (229484278652754012891/100000000000000000000)
  directionLo := (231357650786489642139/100000000000000000000)
  directionHi := (11567882539324482107/5000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree063.table
  base := (-369639028977586520090413598834982308813/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-18596912017806424049677637560320000000000000)
      constant := (397539244370935582350258978096542494043635776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree063.table
  base := (-5914226530291226938144811170638293221547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1563947506267460097473254107400000000000000)
      constant := (33756995915584442153894531041322128445558557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231357650786489642139/100000000000000000000)
  centralHi := (11567882539324482107/5000000000000000000)
  directionLo := (233215975023392708219/100000000000000000000)
  directionHi := (11660798751169635411/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree064.table
  base := (-744066323709539929789730835698581278127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-56659260441139814617611534345120000000000000)
      constant := (1230949260773157068094703388700878652031002656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree064.table
  base := (-5952532254143889483238722289663135451917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1588298657325045400330598640040000000000000)
      constant := (34841684381804594086859609090166930108626027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233215975023392708219/100000000000000000000)
  centralHi := (11660798751169635411/5000000000000000000)
  directionLo := (47011921651759853027/20000000000000000000)
  directionHi := (14691225516174954071/6250000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree065.table
  base := (-5989305060074185152691068955760333978999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (7383)
      previous := (0)
      next := (3381)
      square := (48702302115170605714689065280000000000000)
      linear := (-4425214217604642852783858154560000000000000)
      constant := (97683525052073479224828716135004163697828468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree065.table
  base := (-2994653200185213628501674164763768080841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (207)
      previous := (0)
      next := (92)
      square := (1352841725421405714296918480000000000000)
      linear := (-124049985260202361783687936360000000000000)
      constant := (2764883859525944154473653685916142029898134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47011921651759853027/20000000000000000000)
  centralHi := (14691225516174954071/6250000000000000000)
  directionLo := (47377778699913153221/20000000000000000000)
  directionHi := (118444446749782883053/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree066.table
  base := (-1204909632927282442711553386996863065651/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-19465436405526966518256259224480000000000000)
      constant := (436475808687016442619374172553291808514298860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree066.table
  base := (-602454924369384852951857292022250143497/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1637000959440216006045287705320000000000000)
      constant := (37062413245254293520144697188082397257490070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47377778699913153221/20000000000000000000)
  centralHi := (118444446749782883053/50000000000000000000)
  directionLo := (11935208030457308713/5000000000000000000)
  directionHi := (238704160609146174261/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree067.table
  base := (-3029130080739752965284235877631081290537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-59264833604301442023347399337600000000000000)
      constant := (1349574060355058543596837181008245002856745784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree067.table
  base := (-3029130515027849277884787324298721532499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1661352110497801308902632237960000000000000)
      constant := (38198453554491531474728711722507032122015338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11935208030457308713/5000000000000000000)
  centralHi := (238704160609146174261/100000000000000000000)
  directionLo := (240505727002051849771/100000000000000000000)
  directionHi := (60126431750512962443/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree068.table
  base := (-1522610320680060999053395745339586203317/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-60133357992021984491926021001760000000000000)
      constant := (1390325727146784401657805708848135830156077488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree068.table
  base := (-3045220990872205136994036801171708264501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1685703261555386611759976770600000000000000)
      constant := (39351611063982242705348380825363962606598662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240505727002051849771/100000000000000000000)
  centralHi := (60126431750512962443/25000000000000000000)
  directionLo := (9691755931673387527/4000000000000000000)
  directionHi := (15143368643239668011/6250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree069.table
  base := (-6121091739018881177510476425963347598993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-20333960793247508986834880888640000000000000)
      constant := (477227475051523304012831462245046331069242196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree069.table
  base := (-382568268843000656405572641074625301237/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1710054412612971914617321303240000000000000)
      constant := (40521885739465390679708453868254213185455152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9691755931673387527/4000000000000000000)
  centralHi := (15143368643239668011/6250000000000000000)
  directionLo := (1906788819502652893/781250000000000000)
  directionHi := (48813793779267914061/20000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree070.table
  base := (-1230042344643137905604062467484155372573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-61870406767463069429083264330080000000000000)
      constant := (1473644153205174859565037115718331993566329340) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree070.table
  base := (-6150212175726286974658353762309636237409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1734405563670557217474665835880000000000000)
      constant := (41709277549432651270866779128969671475877879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1906788819502652893/781250000000000000)
  centralHi := (48813793779267914061/20000000000000000000)
  directionLo := (245831222603620496231/100000000000000000000)
  directionHi := (30728902825452562029/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree071.table
  base := (-1235560282649451334303878447486863406159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-62738931155183611897661885994240000000000000)
      constant := (1516210910216033045134378877339669615184643220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree071.table
  base := (-6177801777232444561419151783159008001287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1758756714728142520332010368520000000000000)
      constant := (42913786464685352855637284488046127647782497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245831222603620496231/100000000000000000000)
  centralHi := (30728902825452562029/12500000000000000000)
  directionLo := (9903237324064025719/4000000000000000000)
  directionHi := (7736904159425020093/3125000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree072.table
  base := (-6203860974490276180270249413004481993481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-21202485180968051455413502552800000000000000)
      constant := (519794231726997555017624806360346910517220532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree072.table
  base := (-3101930633609348795323933435255805420751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1783107865785727823189354901160000000000000)
      constant := (44135412457978631212608873462403537767786162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9903237324064025719/4000000000000000000)
  centralHi := (7736904159425020093/3125000000000000000)
  directionLo := (249318364474275526953/100000000000000000000)
  directionHi := (124659182237137763477/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree073.table
  base := (-1557097640412486760766800116390521761919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-64475979930624696834819129322560000000000000)
      constant := (1603159507158827288672699118739340262401939216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree073.table
  base := (-6228390797032148858710388533319930555847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1807459016843313126046699433800000000000000)
      constant := (45374155503734825969195710725028931736061857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249318364474275526953/100000000000000000000)
  centralHi := (124659182237137763477/50000000000000000000)
  directionLo := (50208754333401315061/20000000000000000000)
  directionHi := (125521885833503287653/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree074.table
  base := (-6251390320285861253944506306892707614341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-65344504318345239303397750986720000000000000)
      constant := (1647541345263952358302148532927264766874349356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree074.table
  base := (-3125695254762556269045010496361553670259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1831810167900898428904043966440000000000000)
      constant := (46630015577811896030248117862549794859452458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50208754333401315061/20000000000000000000)
  centralHi := (125521885833503287653/50000000000000000000)
  directionLo := (252757400923226328227/100000000000000000000)
  directionHi := (63189350230806582057/25000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree075.table
  base := (-6272860388049064198851626720200195890923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-22071009568688593923992124216960000000000000)
      constant := (564176069552966304604368716107934002733208156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree075.table
  base := (-784107567520812730072060991068380159751/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1856161318958483731761388499080000000000000)
      constant := (47902992657315595062973631573075550024016648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252757400923226328227/100000000000000000000)
  centralHi := (63189350230806582057/25000000000000000000)
  directionLo := (12722974509733662681/5000000000000000000)
  directionHi := (254459490194673253621/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree076.table
  base := (-1573200223922191862839856562348745425773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-67081553093786324240554994315040000000000000)
      constant := (1738120096548188751991966825043800931318388272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree076.table
  base := (-6292801017947041456201678431017826277403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1880512470016069034618733031720000000000000)
      constant := (49193086720446490594756862600357987359118893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12722974509733662681/5000000000000000000)
  centralHi := (254459490194673253621/100000000000000000000)
  directionLo := (256150269527091175157/100000000000000000000)
  directionHi := (128075134763545587579/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree077.table
  base := (-6311211967875145026814333929108064179627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-67950077481506866709133615979200000000000000)
      constant := (1784317008173328534129362888840566537531149332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree077.table
  base := (-157780301653002644998678687591860042883/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1904863621073654337476077564360000000000000)
      constant := (50500297746374762349465928148799026110110920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256150269527091175157/100000000000000000000)
  centralHi := (128075134763545587579/50000000000000000000)
  directionLo := (128914980711581668053/50000000000000000000)
  directionHi := (257829961423163336107/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree078.table
  base := (-6328093723875093995838725409711224995467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1560000000000000000000000000000000000000000
      center := (2461)
      previous := (0)
      next := (1127)
      square := (16234100705056868571563021760000000000000)
      linear := (-1764579535108395107120826606240000000000000)
      constant := (46951767764325601498657123237365048900707148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree078.table
  base := (-316404690140565844971573897433569446877/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (207)
      previous := (0)
      next := (92)
      square := (1352841725421405714296918480000000000000)
      linear := (-148401136317787664641032469000000000000000)
      constant := (3986509670395167708033329824987271943811980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128914980711581668053/50000000000000000000)
  centralHi := (257829961423163336107/100000000000000000000)
  directionLo := (129749390592151081451/50000000000000000000)
  directionHi := (259498781184302162903/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree079.table
  base := (-49558174047736471557091121115924886763/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-69687126256947951646290859307520000000000000)
      constant := (1878525899758157182005437695147831262583540224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree079.table
  base := (-3171723170761589545825425355691078459471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1953565923188824943190766629640000000000000)
      constant := (53166070607551820926706586748696415480698802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129749390592151081451/50000000000000000000)
  centralHi := (259498781184302162903/100000000000000000000)
  directionLo := (261156937232781113871/100000000000000000000)
  directionHi := (16322308577048819617/6250000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree080.table
  base := (-6357269740620689776866385216651861988227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-70555650644668494114869480971680000000000000)
      constant := (1926537878352221213025510933554690071663626932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree080.table
  base := (-6357269791555601779093134855201264314369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-1977917074246410246048111162280000000000000)
      constant := (54524632405146999827265375348670986330871639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261156937232781113871/100000000000000000000)
  centralHi := (16322308577048819617/6250000000000000000)
  directionLo := (8212644731736658367/3125000000000000000)
  directionHi := (52560926283114613549/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree081.table
  base := (-1273912843490494917989198140111071954207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-23808058344129678861149367545280000000000000)
      constant := (658384959315235326562193569389613730384341020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree081.table
  base := (-6369564258358866510702235381254381045629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2002268225303995548905455694920000000000000)
      constant := (55900311090101619324338133579568009603288699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8212644731736658367/3125000000000000000)
  centralHi := (52560926283114613549/20000000000000000000)
  directionLo := (66110514822787293319/25000000000000000000)
  directionHi := (264442059291149173277/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree082.table
  base := (-6380329810984435957334441677640390214333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-72292699420109579052026724300000000000000000)
      constant := (2024376897915738782730581059866995865935998028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree082.table
  base := (-1276065968766438768634930088626087328103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2026619376361580851762800227560000000000000)
      constant := (57293106645194711143843153253430956207752965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66110514822787293319/25000000000000000000)
  centralHi := (264442059291149173277/100000000000000000000)
  directionLo := (259833408594132571/97656250000000000)
  directionHi := (53213882080078350541/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree083.table
  base := (-79869582752566485870046223011260207389/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-73161223807830121520605345964160000000000000)
      constant := (2074203937660072097634872185876979431859625920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree083.table
  base := (-1597391661644592946041723025617248400741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2050970527419166154620144760200000000000000)
      constant := (58703019053762404112486483831842740081099084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259833408594132571/97656250000000000)
  centralHi := (53213882080078350541/20000000000000000000)
  directionLo := (133843434261341836623/50000000000000000000)
  directionHi := (267686868522683673247/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree084.table
  base := (-399829671309440175987527881325568091741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-24676582731850221329727989209440000000000000)
      constant := (708211998865213396742698014344347966559188032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree084.table
  base := (-6397274762122773351249468466598043505923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2075321678476751457477489292840000000000000)
      constant := (60130048299660910190298709444664930647499013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133843434261341836623/50000000000000000000)
  centralHi := (267686868522683673247/100000000000000000000)
  directionLo := (67323652979538409471/25000000000000000000)
  directionHi := (53858922383630727577/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree085.table
  base := (-6403454266109434007125856594521794334703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-74898272583271206457762589292480000000000000)
      constant := (2175673074157313525841298712228029403267666948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree085.table
  base := (-1600863570775849777735680790584319010583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2099672829534336760334833825480000000000000)
      constant := (61574194367234407281537892018965000348845892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67323652979538409471/25000000000000000000)
  centralHi := (53858922383630727577/20000000000000000000)
  directionLo := (135446406778490635169/50000000000000000000)
  directionHi := (270892813556981270339/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree086.table
  base := (-320405264289921247731115125535255270989/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-75766796970991748926341210956640000000000000)
      constant := (2227315169796814603077304394974790138626058480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree086.table
  base := (-3204052649718619583400496615141384127589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2124023980591922063192178358120000000000000)
      constant := (63035457241286924058703348594882212164874918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135446406778490635169/50000000000000000000)
  centralHi := (270892813556981270339/100000000000000000000)
  directionLo := (27248164133659694269/10000000000000000000)
  directionHi := (272481641336596942691/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree087.table
  base := (-6411227887522503521847522924284068111253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-25545107119570763798306610873600000000000000)
      constant := (759854094327255372591408602247971909870378916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree087.table
  base := (-6411227898467184943123786506634859285643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2148375131649507366049522890760000000000000)
      constant := (64513836907057511871088462348098708780726333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27248164133659694269/10000000000000000000)
  centralHi := (272481641336596942691/100000000000000000000)
  directionLo := (54812251657509672459/20000000000000000000)
  directionHi := (34257657285943545287/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree088.table
  base := (-6412822156311242654598621553012005143683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-77503845746432833863498454284960000000000000)
      constant := (2332414413194848148129833368516594960705832628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree088.table
  base := (-400801385318304782900868308175343383419/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2172726282707092668906867423400000000000000)
      constant := (66009333350198131544074261778853871491235024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54812251657509672459/20000000000000000000)
  centralHi := (34257657285943545287/12500000000000000000)
  directionLo := (34453977846093551629/12500000000000000000)
  directionHi := (275631822768748413033/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree089.table
  base := (-801611021855373168117298231778281408157/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-78372370134153376332077075949120000000000000)
      constant := (2385871559933045655380417081402387487302182496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree089.table
  base := (-6412888181888200609876861028999619895613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2197077433764677971764211956040000000000000)
      constant := (67521946556753796226509009186219064237641403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34453977846093551629/12500000000000000000)
  centralHi := (275631822768748413033/100000000000000000000)
  directionLo := (138596744326383056873/50000000000000000000)
  directionHi := (277193488652766113747/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree090.table
  base := (-1602856505889039245753695093813158767427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-26413631507291306266885232537760000000000000)
      constant := (813311240902323753150772243031787656078632176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree090.table
  base := (-3205713014603810551327942473111951563279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2221428584822263274621556488680000000000000)
      constant := (69051676513144601517747504759688160371611698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138596744326383056873/50000000000000000000)
  centralHi := (277193488652766113747/100000000000000000000)
  directionLo := (69686601375443586973/25000000000000000000)
  directionHi := (278746405501774347893/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree091.table
  base := (-3204217890375098667867515741110783211539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (7383)
      previous := (0)
      next := (3381)
      square := (48702302115170605714689065280000000000000)
      linear := (-6162262993045727789941101482880000000000000)
      constant := (191892377003096243754128365106460306913999496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree091.table
  base := (-160210894632077515518654817258275131443/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (207)
      previous := (0)
      next := (92)
      square := (1352841725421405714296918480000000000000)
      linear := (-172752287375372967498377001640000000000000)
      constant := (5430655631242257364283581151225696931649640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69686601375443586973/25000000000000000000)
  centralHi := (278746405501774347893/100000000000000000000)
  directionLo := (140145359367361908223/50000000000000000000)
  directionHi := (280290718734723816447/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree092.table
  base := (-25615670090710887109701729317542523633/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-80977943297315003737812940941600000000000000)
      constant := (2549873094468964471497071965717777821554207000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree092.table
  base := (-1280783505262606747619033632307292129913/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2270130886937433880336245553960000000000000)
      constant := (72162486622890500197329051925820338150223515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140145359367361908223/50000000000000000000)
  centralHi := (280290718734723816447/100000000000000000000)
  directionLo := (281826569786272097701/100000000000000000000)
  directionHi := (140913284893136048851/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree093.table
  base := (-3198935661814608049208857406303906533053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-27282155895011848735463854201920000000000000)
      constant := (868583434180375950661382710080771355101937032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree093.table
  base := (-6397871326544344127613427369441305516917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2294482037995019183193590086600000000000000)
      constant := (73743566750820334801953101533724419367641027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281826569786272097701/100000000000000000000)
  centralHi := (140913284893136048851/50000000000000000000)
  directionLo := (141677048128979713889/50000000000000000000)
  directionHi := (283354096257959427779/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree094.table
  base := (-1278059451202265074493085947058835025349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-82714992072756088674970184269920000000000000)
      constant := (2662232524816219281636180636869670238528883420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree094.table
  base := (-6390297258348683376420168622373201488633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2318833189052604486050934619240000000000000)
      constant := (75341763577708040431335559275538928948421023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141677048128979713889/50000000000000000000)
  centralHi := (283354096257959427779/100000000000000000000)
  directionLo := (284873432062088543889/100000000000000000000)
  directionHi := (28487343206208854389/10000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree095.table
  base := (-199412355950612574493093653692281027763/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-83583516460476631143548805934080000000000000)
      constant := (2719319760864735417314033291410657191266877056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree095.table
  base := (-1276239078458699616573919481786855192629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2343184340110189788908279151880000000000000)
      constant := (76957077091627718610354564423690107362228495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284873432062088543889/100000000000000000000)
  centralHi := (28487343206208854389/10000000000000000000)
  directionLo := (57276941511746877617/20000000000000000000)
  directionHi := (143192353779367194043/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree096.table
  base := (-3185282897853212502431799079782951111309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-28150680282732391204042475866080000000000000)
      constant := (925670670089259464013794855934640350292530696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree096.table
  base := (-3185282898604297467892835964291172465569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2367535491167775091765623684520000000000000)
      constant := (78589507280947132008598868042469583706637678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57276941511746877617/20000000000000000000)
  centralHi := (143192353779367194043/50000000000000000000)
  directionLo := (17993003105392525567/6250000000000000000)
  directionHi := (287888049686280409073/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree097.table
  base := (-6358408539044666741043764884746424784033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-85320565235917716080706049262400000000000000)
      constant := (2835309272616668443411840016858462751613943228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree097.table
  base := (-6358408540248723788375602231822504618521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2391886642225360394622968217160000000000000)
      constant := (80239054134317127900876451633341996719469951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17993003105392525567/6250000000000000000)
  centralHi := (287888049686280409073/100000000000000000000)
  directionLo := (36172947760731425521/12500000000000000000)
  directionHi := (289383582085851404169/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree098.table
  base := (-6344723685987604113585291478307177452923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-86189089623638258549284670926560000000000000)
      constant := (2894211547512579437070018545538299132376416468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree098.table
  base := (-6344723686952610683466010410846202204569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2416237793282945697480312749800000000000000)
      constant := (81905717640661661585949616062726991827427839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36172947760731425521/12500000000000000000)
  centralHi := (289383582085851404169/100000000000000000000)
  directionLo := (145435712609994057389/50000000000000000000)
  directionHi := (290871425219988114779/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree099.table
  base := (-6329511300525463633436350186403212119809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-29019204670452933672621097530240000000000000)
      constant := (984572944855398278307770491299274285821027348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree099.table
  base := (-3164755650649400967165855219763250669513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2440588944340531000337657282440000000000000)
      constant := (83589497789168358736874917769040021273704606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145435712609994057389/50000000000000000000)
  centralHi := (290871425219988114779/100000000000000000000)
  directionLo := (292351696485885947883/100000000000000000000)
  directionHi := (73087924121471486971/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree100.table
  base := (-315638572256947292162757731874357968067/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-87926138399079343486441914254880000000000000)
      constant := (3013831133397382054870186230221528122445607440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree100.table
  base := (-6312771445758623205340263893267690034197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2464940095398116303195001815080000000000000)
      constant := (85290394569279565316374238846037760384220707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree100.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292351696485885947883/100000000000000000000)
  centralHi := (73087924121471486971/25000000000000000000)
  directionLo := (146912255161749540709/50000000000000000000)
  directionHi := (293824510323499081419/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree101.table
  base := (-3147252090425005557092027178888495879489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-88794662786799885955020535919040000000000000)
      constant := (3074548443634883490012612759991904782138377848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree101.table
  base := (-6294504181346511284065876018116963296469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2489291246455701606052346347720000000000000)
      constant := (87008407970683841507347538607138233202896739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree101.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146912255161749540709/50000000000000000000)
  centralHi := (293824510323499081419/100000000000000000000)
  directionLo := (295289978318791676621/100000000000000000000)
  directionHi := (147644989159395838311/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree102.table
  base := (-6274709567270169061626188128302490280471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-29887729058173476141199719194400000000000000)
      constant := (1045290254972007571950159455621722549711204812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree102.table
  base := (-784338695958492335268562017535850908791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2513642397513286908909690880360000000000000)
      constant := (88743537983307862455327665616211529571314568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree102.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295289978318791676621/100000000000000000000)
  centralHi := (147644989159395838311/50000000000000000000)
  directionLo := (296748209302399832757/100000000000000000000)
  directionHi := (148374104651199916379/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree103.table
  base := (-6253387662646478591558232307241201934447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60840000000000000000000000000000000000000000
      center := (95979)
      previous := (0)
      next := (43953)
      square := (633129927497217874290957848640000000000000)
      linear := (-90531711562240970892177779247360000000000000)
      constant := (3197798096886424625999820951878164527430824452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree103.table
  base := (-195418364467660018517947034374660788231/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2537993548570872211767035413000000000000000)
      constant := (90495784597308693792699955311261834457246752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree103.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296748209302399832757/100000000000000000000)
  centralHi := (148374104651199916379/50000000000000000000)
  directionLo := (298199309443951158891/100000000000000000000)
  directionHi := (74549827360987789723/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree104.table
  base := (-1557634630976359278670126518395418293629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4680000000000000000000000000000000000000000
      center := (7383)
      previous := (0)
      next := (3381)
      square := (48702302115170605714689065280000000000000)
      linear := (-7030787380766270258519723147040000000000000)
      constant := (250794649169211416170303059472763776954326512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree104.table
  base := (-3115269262080334336936641124227275520533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130000000000000000000000000000000000000000
      center := (207)
      previous := (0)
      next := (92)
      square := (1352841725421405714296918480000000000000)
      linear := (-197103438432958270355721534280000000000000)
      constant := (7097319061774339549936372398610090836466142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree104.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298199309443951158891/100000000000000000000)
  centralHi := (74549827360987789723/25000000000000000000)
  directionLo := (1498216911711366471/500000000000000000)
  directionHi := (299643382342273294201/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 156
  table := BinomialMassData.Q107_156.Degree105.table
  base := (-3103081103347457051889754546609491865143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 20280000000000000000000000000000000000000000
      center := (31993)
      previous := (0)
      next := (14651)
      square := (211043309165739291430319282880000000000000)
      linear := (-30756253445894018609778340858560000000000000)
      constant := (1107822597172477476873467255567051900994979992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_156.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9
  qDenominator := 13
  table := BinomialMassData.Q9_13.Degree105.table
  base := (-1241232441379867104211843868017956381387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (1196)
      square := (17586942430478274285859940240000000000000)
      linear := (-2586695850686042817481724478280000000000000)
      constant := (94051627591177060336188992421724826857727985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_13.Degree105.checked
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
end ForestUnimodality.Stage170KernelData.Cell346.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell346
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 105 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 105 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 105 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel105.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell346

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel106
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  degreePropagationTail 106 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel107
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  degreePropagationTail 107 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel108
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  degreePropagationTail 108 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel109
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  degreePropagationTail 109 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel110
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  degreePropagationTail 110 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel111
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  degreePropagationTail 111 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel112
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  degreePropagationTail 112 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel113
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  degreePropagationTail 113 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel114
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  degreePropagationTail 114 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell346.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 105 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell346.Kernel349

